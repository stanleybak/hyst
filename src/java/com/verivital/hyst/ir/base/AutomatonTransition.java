package com.verivital.hyst.ir.base;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Map.Entry;

import com.verivital.hyst.grammar.formula.Constant;
import com.verivital.hyst.grammar.formula.DefaultExpressionPrinter;
import com.verivital.hyst.grammar.formula.Expression;
import com.verivital.hyst.ir.AutomatonExportException;
import com.verivital.hyst.ir.AutomatonValidationException;
import com.verivital.hyst.ir.Configuration;
import com.verivital.hyst.util.AutomatonUtil;

/**
 * A transition in a hybrid automaton.
 * 
 * automaton, from and to, and guard are nonnull reset is nonnull as well, but
 * may be empty Label may be null (if no label), but not blank ("")
 * 
 * @author Stanley Bak (stanleybak@gmail.com)
 *
 */
public class AutomatonTransition
{
	public static final Expression DEFAULT_GUARD = Constant.TRUE;

	public BaseComponent parent;
	public AutomatonMode from;
	public AutomatonMode to;
	public String label;

	public Expression guard;
	public LinkedHashMap<String, ExpressionInterval> reset; // if x' := x + 1,
															// then x maps to x
															// + 1

	/**
	 * The way to create a new transition in a hybrid automaton is to do
	 * HybridAutomaton.createTransition(from, to), which will manage the
	 * internal state of the automaton Guard is initially null, be sure to set
	 * it
	 * 
	 * @param parent
	 *            the hybrid automaton
	 * @param from
	 *            the mode the transition comes from
	 * @param to
	 *            to mode the transition goes to
	 */
	protected AutomatonTransition(BaseComponent parent, AutomatonMode from, AutomatonMode to)
	{
		this.parent = parent;
		this.from = from;
		this.to = to;

		reset = new LinkedHashMap<String, ExpressionInterval>();
	}

	/**
	 * Deep copy. This also updates the transitions in the passed-in parent
	 * HybridAutomaton
	 */
	public AutomatonTransition copy(BaseComponent parent)
	{
		// parent may be different, so search for from.name and to.name in
		// parent
		AutomatonMode parentFrom = null, parentTo = null;

		for (AutomatonMode am : parent.modes.values())
		{
			if (am.name.equals(from.name))
				parentFrom = am;

			if (am.name.equals(to.name))
				parentTo = am;
		}

		if (parentFrom == null)
			throw new AutomatonExportException("Source mode ('" + from.name
					+ "') not found in parent automaton: " + parent.getPrintableInstanceName());

		if (parentTo == null)
			throw new AutomatonExportException("Destination mode ('" + to.name
					+ "') not found in parent automaton: " + parent.getPrintableInstanceName());

		AutomatonTransition rv = parent.createTransition(parentFrom, parentTo);

		rv.guard = guard.copy();

		for (Entry<String, ExpressionInterval> e : reset.entrySet())
			rv.reset.put(e.getKey(), e.getValue().copy());

		rv.label = label;

		return rv;
	}

	/**
	 * Check if the guarantees expected of this class are met. This is run prior
	 * to any printing procedures.
	 * 
	 * @throws AutomatonValidationException
	 *             if guarantees are violated
	 */
	public void validate()
	{
		if (!Configuration.DO_VALIDATION)
			return;

		if (parent == null)
			throw new AutomatonValidationException("automaton was null");

		if (from == null)
			throw new AutomatonValidationException("from was null");

		if (to == null)
			throw new AutomatonValidationException("to was null");

		if (parent.modes.get(from.name) == null)
			throw new AutomatonValidationException("mode '" + from.name + "' in" + " transition '"
					+ from.name + "'->'" + to.name + "' does not exist in parent");

		if (parent.modes.get(to.name) == null)
			throw new AutomatonValidationException("mode '" + to.name + "' in" + " transition '"
					+ from.name + "'->'" + to.name + "' does not exist in parent");

		if (guard == null)
			throw new AutomatonValidationException("guard was null");

		if (reset == null)
			throw new AutomatonValidationException("reset was null");

		if (label != null && label.length() == 0)
			throw new AutomatonValidationException("label was blank");

		if (guard == null)
			throw new AutomatonValidationException(
					"transition guard is null: " + from.name + " -> " + to.name);

		for (Entry<String, ExpressionInterval> e : reset.entrySet())
		{
			if (e.getValue() == null)
				throw new AutomatonValidationException("transition reset is null for variable "
						+ e.getKey() + ": " + from.name + " -> " + to.name);
		}

		ArrayList<String> validVarNames = new ArrayList<String>();
		validVarNames.addAll(parent.variables);
		validVarNames.addAll(parent.constants.keySet());

		checkOnlyUsesAllowedVariables(validVarNames);
	}

	/**
	 * Validation check that the expressions in this transition only use
	 * variables/constants defined in the automaton
	 * 
	 * @param validVarNames
	 *            the list of variables / constants which are allowed
	 */
	private void checkOnlyUsesAllowedVariables(ArrayList<String> validVarNames)
	{
		for (String var : AutomatonUtil.getVariablesInExpression(guard))
		{
			if (!validVarNames.contains(var))
				throw new AutomatonValidationException(
						"Invariant in transition " + from.name + "->" + to.name + " used variable "
								+ var + " which was not defined in component.");
		}

		for (Entry<String, ExpressionInterval> e : reset.entrySet())
		{
			if (!parent.variables.contains(e.getKey()))
			{
				throw new AutomatonValidationException(
						"transition " + from.name + "->" + to.name + " resets variable "
								+ e.getKey() + " which was not defined in component.");
			}

			for (String var : AutomatonUtil.getVariablesInExpression(e.getValue().getExpression()))
			{
				if (!validVarNames.contains(var))
					throw new AutomatonValidationException("reset for " + var + " in transition "
							+ from.name + "->" + to.name + " used variable " + var
							+ " which was not defined in component.");
			}
		}
	}

	public String toString()
	{
		return "[AutomatonTransition from:" + from.name + ", to: " + to.name + ", label: " + label
				+ ", guard: " + DefaultExpressionPrinter.instance.print(guard) + ", reset: "
				+ AutomatonUtil.getMapExpressionIntervalString(reset) + "]";
	}
}
