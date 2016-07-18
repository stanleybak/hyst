package com.verivital.hyst.passes.complex;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;

import org.kohsuke.args4j.Option;

import com.verivital.hyst.geometry.HyperPoint;
import com.verivital.hyst.geometry.Interval;
import com.verivital.hyst.geometry.SymbolicStatePoint;
import com.verivital.hyst.grammar.formula.Constant;
import com.verivital.hyst.grammar.formula.Expression;
import com.verivital.hyst.grammar.formula.Operation;
import com.verivital.hyst.grammar.formula.Operator;
import com.verivital.hyst.grammar.formula.Variable;
import com.verivital.hyst.internalpasses.DeleteParams;
import com.verivital.hyst.ir.AutomatonExportException;
import com.verivital.hyst.ir.Configuration;
import com.verivital.hyst.ir.base.AutomatonMode;
import com.verivital.hyst.ir.base.AutomatonTransition;
import com.verivital.hyst.ir.base.BaseComponent;
import com.verivital.hyst.ir.base.ExpressionInterval;
import com.verivital.hyst.ir.base.ExpressionModifier;
import com.verivital.hyst.main.Hyst;
import com.verivital.hyst.passes.TransformationPass;
import com.verivital.hyst.passes.complex.ContinuizationPass.IntervalTerm;
import com.verivital.hyst.printers.PySimPrinter;
import com.verivital.hyst.printers.PySimPrinter.PySimExpressionPrinter;
import com.verivital.hyst.python.PythonBridge;
import com.verivital.hyst.util.AutomatonUtil;
import com.verivital.hyst.util.Preconditions.PreconditionsFailedException;
import com.verivital.hyst.util.StringOperations;
import com.verivital.hyst.util.ValueSubstituter;

/**
 * This is the enhanced version of the continuization pass that uses
 * time-triggered guards.
 * 
 * This expects the single-mode periodically-sampled CPS as input. From this it
 * extracts the period, cyber-var, time-var.
 * 
 * @author Stanley Bak (June 2016)
 *
 */
public class ContinuizationPassTT extends TransformationPass
{
	private static class DomainValues
	{
		double startTime;
		double endTime;

		double bloat; // bloating term for this domain
		Interval range; // simulated range + bloating term
		AutomatonMode mode;

		public String toString()
		{
			return "[DomainValue mode: " + (mode == null ? "null" : mode.name) + ", times = "
					+ startTime + "-" + endTime + ", range = " + range + "]";
		}
	}

	ArrayList<DomainValues> domains = new ArrayList<DomainValues>();

	@Option(name = "-noerrormodes", usage = "skip creating error modes")
	boolean skipErrorModes = false;

	@Option(name = "-timestep", usage = "time step for creating time-triggered domains", metaVar = "TIME")
	double timeStep;

	@Option(name = "-bloat", required = true, usage = "bloating term for each time domain", metaVar = "VAL")
	double bloat;

	BaseComponent ha = null;
	AutomatonMode am = null;

	String timeVar = null;
	String clockVar = null;
	String cyberVar = null;
	Expression cyberExpression = null;
	double period = 0;
	HashMap<String, ExpressionInterval> originalDynamics = new HashMap<String, ExpressionInterval>();

	private void processParams()
	{
		// find cyberVar and clockVar. They are in the reset. Cyber is set to
		// non-zero, clock is set to zero.
		AutomatonTransition at = ha.transitions.get(0);
		AutomatonMode am = ha.modes.values().iterator().next();

		if (!(at.guard instanceof Operation) || at.guard.asOperation().op != Operator.GREATEREQUAL
				|| !(at.guard.asOperation().getLeft() instanceof Variable)
				|| !(at.guard.asOperation().getRight() instanceof Constant))
			throw new AutomatonExportException(
					"excepted guard to be of form clock_var >= PERIOD. Got: "
							+ at.guard.toDefaultString());

		clockVar = ((Variable) at.guard.asOperation().getLeft()).name;
		period = ((Constant) at.guard.asOperation().getRight()).getVal();

		// extract cyber variable expression from reset
		for (Entry<String, ExpressionInterval> e : at.reset.entrySet())
		{
			if (e.getValue().getInterval() != null)
				throw new AutomatonExportException(
						"Reset for '" + e.getKey() + "' cannot contain interval assignment.");

			if (e.getKey().equals(clockVar))
			{
				if (!e.getValue().asExpression().equals(new Constant(0)))
					throw new AutomatonExportException(
							"Clock Reset for '" + clockVar + "' must be to zero.");
			}
			else if (cyberVar != null)
				throw new AutomatonExportException(
						"Reset assigns to more than one cyber variable?");
			else
			{
				cyberVar = e.getKey();
				cyberExpression = e.getValue().asExpression();
			}
		}

		if (cyberVar == null)
			throw new AutomatonExportException("Couldn't find cyber variable assignment in reset.");

		if (checkClockVariableInInvariant(am.invariant, clockVar) == false)
			throw new AutomatonExportException("Couldn't find clock condition in invariant: "
					+ am.invariant.toDefaultString());

		// find timeVar
		for (Entry<String, ExpressionInterval> e : am.flowDynamics.entrySet())
		{
			ExpressionInterval val = e.getValue();

			if (!e.getKey().equals(cyberVar) && !e.getKey().equals(clockVar)
					&& val.getInterval() == null && val.getExpression() instanceof Constant
					&& ((Constant) val.asExpression()).getVal() == 1)
			{
				timeVar = e.getKey();
			}
		}

		if (timeVar == null)
			throw new AutomatonExportException("Couldn't find time variable in automaton.");

		// create domain values
		double lastTime = 0;
		double TOL = 1e-9;

		for (double t = timeStep; lastTime + period
				+ TOL < config.settings.spaceExConfig.timeHorizon; t += timeStep)
		{
			DomainValues dv = new DomainValues();
			domains.add(dv);

			dv.startTime = lastTime;
			dv.endTime = t;

			lastTime = Math.max(0, t - period);

			dv.bloat = bloat;
		}
	}

	/**
	 * Checks if the inverse of the clock guard exists in the invariant
	 * 
	 * @param inv
	 *            the invariant expression
	 * @return true iff the clock condition exists in the invariant
	 */
	private boolean checkClockVariableInInvariant(Expression inv, String clockVar)
	{
		boolean found = false;

		if (inv instanceof Operation)
		{
			Operation o = inv.asOperation();

			if (o.op.equals(Operator.AND))
			{
				for (Expression child : o.children)
					found = found || checkClockVariableInInvariant(child, clockVar);
			}
			else if (o.op.equals(Operator.LESSEQUAL) && o.getLeft() instanceof Variable
					&& ((Variable) o.getLeft()).name.equals(clockVar))
			{
				if (o.getRight() instanceof Constant
						&& ((Constant) o.getRight()).getVal() == period)
					found = true;
				else
					throw new AutomatonExportException(
							"Clock guard and invariant do not match. Expected " + clockVar + " <= "
									+ period + "; Invariant contained " + inv.toDefaultString());
			}
		}

		return found;
	}

	public static String makeParamString(boolean skipError, double step, double bloat)
	{
		StringBuilder rv = new StringBuilder();

		if (skipError == true)
			rv.append("-noerrormodes ");

		rv.append("-timestep ");
		rv.append(step);

		rv.append(" -bloat ");
		rv.append(bloat);

		return rv.toString();
	}

	@Override
	public String getCommandLineFlag()
	{
		return "-pass_continuization_tt";
	}

	@Override
	public String getName()
	{
		return "Continuization Pass (Time-Triggered)";
	}

	@Override
	public String getLongHelp()
	{
		String header = "Currently, this pass assumes a one-mode automaton, which is the periodically-actuated CPS."
				+ " There must be a single transition, which has a reset for the the actuation of the cyber variable.";

		return header;
	}

	@Override
	protected void checkPreconditons(Configuration c, String name)
	{
		super.checkPreconditons(c, name);
		BaseComponent ha = ((BaseComponent) c.root);

		// make sure it's a continuous approximation (single mode)
		if (ha.modes.size() != 1 || ha.transitions.size() != 1)
			throw new PreconditionsFailedException(
					"Automaton must be the periodically-sampled automaton "
							+ "(single mode with single transition) for " + name + ".");
	}

	/**
	 * Make the automaton into a contiunized approximation. This involves
	 * removing the clock and cyber variable, and substituting the cyber
	 * variable expression for every occurance of the cyber variable.
	 */
	private void makeContinuizedApprox()
	{
		ha.transitions.clear();

		// store original dynamics
		for (Entry<String, ExpressionInterval> e : am.flowDynamics.entrySet())
		{
			if (!e.getKey().equals(cyberVar) && !e.getKey().equals(clockVar))
				originalDynamics.put(e.getKey(), e.getValue().copy());
		}

		// substitute every occurrence of cyberVar with cyberExpression
		createModifiedDynamicsInMode(am, null);

		DeleteParams.run(config, clockVar, cyberVar);

		config.validate();
	}

	/**
	 * Modify the dynamics to be originalDynamics but cyberVar replaced by
	 * cyberExpression + omega
	 * 
	 * @param omaga
	 *            the interval in the substitution (can be null)
	 */
	private void createModifiedDynamicsInMode(AutomatonMode mode, Interval omega)
	{
		HashMap<String, Expression> subs = new HashMap<String, Expression>();

		if (omega == null)
			subs.put(cyberVar, cyberExpression);
		else
			subs.put(cyberVar,
					new Operation(Operator.ADD, cyberExpression, new IntervalTerm(omega)));

		final ValueSubstituter vs = new ValueSubstituter(subs);

		// copy from originalDynamics
		mode.flowDynamics.clear();

		for (Entry<String, ExpressionInterval> e : originalDynamics.entrySet())
			mode.flowDynamics.put(e.getKey(), e.getValue().copy());

		ExpressionModifier.modifyBaseComponent(ha, new ExpressionModifier()
		{
			@Override
			public Expression modifyExpression(Expression e)
			{
				return vs.substitute(e);
			}
		});

		// substitute out the IntervalTerms

		for (Entry<String, ExpressionInterval> e : mode.flowDynamics.entrySet())
		{
			ExpressionInterval ei = ContinuizationPass
					.simplifyExpressionWithIntervals(e.getValue().asExpression());

			if (ei.getInterval() != null)
				e.setValue(ei);
		}
	}

	@Override
	public void runPass()
	{
		ha = (BaseComponent) config.root;
		am = ha.modes.values().iterator().next();

		processParams();

		makeContinuizedApprox();

		// estimate ranges based on simulation, stored in domains.ranges
		estimateRanges();

		createModesWithTimeConditions();

		// substitute every with cyberExp + \omega_i
		substituteOriginalCyberVariables();

		// add the range conditions to each of the modes
		if (skipErrorModes == false)
			addRangeConditionsToModes(ha);

		// enable time-triggered transitions
		config.settings.spaceExConfig.timeTriggered = true;
	}

	/**
	 * substitute every occurrence of cyberVar with cyberVarExpression +
	 * \omega_i
	 */
	private void substituteOriginalCyberVariables()
	{
		for (DomainValues dv : domains)
		{
			AutomatonMode am = dv.mode;

			Interval K = dv.range;
			Interval omega = Interval.mult(K, new Interval(-period, 0));

			Hyst.log("bloated sim range in time [" + dv.startTime + ", " + dv.endTime + "] was " + K
					+ ", omega was " + omega);

			createModifiedDynamicsInMode(am, omega);

			Hyst.log("Created dynamcis: " + am);
		}
	}

	private void addRangeConditionsToModes(BaseComponent ha)
	{
		for (DomainValues dv : domains)
		{
			AutomatonMode am = dv.mode;

			// add checks that the candidate derivatives domains are maintained
			Expression maxDerivative = new Operation(Operator.ADD, cyberExpression,
					new Constant(bloat));
			Expression minDerivative = new Operation(Operator.SUBTRACT, cyberExpression,
					new Constant(bloat));

			AutomatonMode errorModeAbove = getErrorMode(ha, "error_" + am.name + "_above");
			AutomatonTransition t1 = ha.createTransition(am, errorModeAbove);
			t1.guard = new Operation(Operator.GREATEREQUAL, maxDerivative,
					new Constant(dv.range.max));

			AutomatonMode errorModeBelow = getErrorMode(ha, "error_" + am.name + "_below");
			AutomatonTransition t2 = ha.createTransition(am, errorModeBelow);
			t2.guard = new Operation(Operator.LESSEQUAL, minDerivative, new Constant(dv.range.min));
		}
	}

	/**
	 * Create modes for the disjoint time condition. Store in params.modes
	 * 
	 * @param params
	 *            the ParamValues instance
	 * @param mode
	 *            the automaton mode we're continuizing
	 */
	private void createModesWithTimeConditions()
	{
		AutomatonMode mode = ha.modes.values().iterator().next();

		// make all the modes
		for (int i = 0; i < domains.size(); ++i)
		{
			DomainValues dv = domains.get(i);
			AutomatonMode newMode = mode;

			if (i != 0)
				newMode = mode.copy(ha, mode.name + "_" + (i + 1));

			dv.mode = newMode;
		}

		// update the invariants and transitions for each mode
		for (int i = 0; i < domains.size(); ++i)
		{
			DomainValues dv = domains.get(i);
			double minTime = dv.startTime;
			double maxTime = dv.endTime;
			AutomatonMode am = dv.mode;

			Operation minTimeCond = new Operation(Operator.GREATEREQUAL, new Variable(timeVar),
					new Constant(minTime));
			Operation maxTimeCond = new Operation(Operator.LESSEQUAL, new Variable(timeVar),
					new Constant(maxTime));

			Operation timeCond = new Operation(Operator.AND, minTimeCond, maxTimeCond);

			// update invariant
			am.invariant = new Operation(Operator.AND, am.invariant, timeCond);

			// add the outgoing time transition
			if (i + 1 < domains.size())
			{
				AutomatonMode nextAm = domains.get(i + 1).mode;

				AutomatonTransition at = ha.createTransition(am, nextAm);
				at.guard = new Operation(Operator.GREATEREQUAL, new Variable(timeVar),
						new Constant(maxTime));
			}
		}
	}

	private AutomatonMode getErrorMode(BaseComponent ha, String badModeName)
	{
		AutomatonMode rv = null;

		if (ha.modes.containsKey(badModeName))
			rv = ha.modes.get(badModeName);
		else
		{
			rv = ha.createMode(badModeName);

			rv.invariant = Constant.TRUE;

			for (String v : ha.variables)
				rv.flowDynamics.put(v, new ExpressionInterval(new Constant(0)));

			// update forbidden states
			config.forbidden.put(badModeName, Constant.TRUE);
		}

		return rv;
	}

	/**
	 * Estimate ranges of the cyber variable derivative in each region and store
	 * in domains.ranges
	 * 
	 * @param ha
	 *            the two-mode automaton
	 * @param params
	 *            <in/out> the time divisions and where the resultant ranges are
	 *            stored
	 */
	private void estimateRanges()
	{
		// simulate from initial state
		HyperPoint initPt = AutomatonUtil.getInitialPoint((BaseComponent) config.root, config);
		String initMode = config.init.keySet().iterator().next();
		Hyst.log("Init point from config: '" + initMode + "' with " + initPt);

		List<Interval> simTimes = new ArrayList<Interval>();

		for (DomainValues d : domains)
		{
			simTimes.add(new Interval(d.startTime, d.endTime));
		}

		SymbolicStatePoint start = new SymbolicStatePoint(initMode, initPt);
		List<Interval> ranges = pythonSimulateExpressionRange(config, start, simTimes,
				cyberExpression);

		if (ranges.size() != domains.size())
			throw new AutomatonExportException(
					"expected single range for each domain from simulation");

		for (int index = 0; index < domains.size(); ++index)
		{
			DomainValues dv = domains.get(index);
			dv.range = ranges.get(index);
		}

		Hyst.log("Ranges from simulation were:");
		logAllRanges();

		// bloat ranges
		for (DomainValues dv : domains)
		{
			dv.range.max += dv.bloat;
			dv.range.min -= dv.bloat;
		}

		Hyst.log("Ranges after bloating were:");
		logAllRanges();
	}

	private void logAllRanges()
	{
		for (DomainValues dv : domains)
			Hyst.log("time [" + dv.startTime + ", " + dv.endTime + "]: " + dv.range);
	}

	/**
	 * Simulate the automaton, getting the range of the derivative of a variable
	 * 
	 * @param automaton
	 * @param derVarName
	 *            the variable name whose derative we want the range of
	 * @param start
	 *            the start state
	 * @param timeIntervals
	 *            the times where to return the ranges
	 * @return the range of the derivative of derVarName
	 */
	public static ArrayList<Interval> pythonSimulateExpressionRange(Configuration automaton,
			SymbolicStatePoint start, List<Interval> timeIntervals, Expression expToEavl)
	{
		PySimExpressionPrinter pyPrinter = new PySimExpressionPrinter();
		pyPrinter.ha = (BaseComponent) automaton.root;

		int numVars = automaton.root.variables.size();

		if (start.hp.dims.length != numVars)
			throw new AutomatonExportException(
					"start point had " + start.hp.dims.length + " dimensions; expected " + numVars);

		PythonBridge pb = PythonBridge.getInstance();
		pb.send("from pythonbridge.pysim_utils import simulate_exp_range");

		StringBuilder s = new StringBuilder();
		s.append(PySimPrinter.automatonToString(automaton));

		String point = "[" + StringOperations.join(",", start.hp.dims) + "]";
		ArrayList<String> intervalStrs = new ArrayList<String>();

		for (Interval i : timeIntervals)
			intervalStrs.add("(" + i.min + "," + i.max + ")");

		String timesStr = "[" + StringOperations.join(",", intervalStrs.toArray(new String[0]))
				+ "]";

		s.append("def eval_expression(state):\n");
		s.append("    return " + pyPrinter.print(expToEavl) + "\n\n");

		s.append("print simulate_exp_range(define_ha(), eval_expression, '" + start.modeName + "', "
				+ point + ", " + timesStr + ")");

		String result = pb.send(s.toString());

		// result is semi-colon separated hyperrectangles
		// each hyperrectangle is a comma-separated list of size 2*N (N = number
		// of dimensions)

		ArrayList<Interval> rv = new ArrayList<Interval>();

		for (String part : result.split(";"))
		{
			String[] comma_parts = part.split(",");

			if (comma_parts.length != 2)
				throw new AutomatonExportException(
						"Result interval had " + comma_parts.length + " parts, expected 2");

			Interval i = new Interval();

			i.min = Double.parseDouble(comma_parts[0]);
			i.max = Double.parseDouble(comma_parts[1]);

			rv.add(i);

			Hyst.log("Simulated Range for domain " + rv.size() + " was [" + i.min + ", " + i.max
					+ "]");
		}

		return rv;
	}
}
