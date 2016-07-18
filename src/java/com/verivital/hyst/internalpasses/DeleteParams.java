package com.verivital.hyst.internalpasses;

import com.verivital.hyst.grammar.formula.Constant;
import com.verivital.hyst.grammar.formula.Expression;
import com.verivital.hyst.grammar.formula.Operation;
import com.verivital.hyst.grammar.formula.Operator;
import com.verivital.hyst.grammar.formula.Variable;
import com.verivital.hyst.ir.AutomatonExportException;
import com.verivital.hyst.ir.Component;
import com.verivital.hyst.ir.Configuration;
import com.verivital.hyst.ir.base.AutomatonMode;
import com.verivital.hyst.ir.base.AutomatonTransition;
import com.verivital.hyst.ir.base.BaseComponent;
import com.verivital.hyst.ir.base.ExpressionModifier;

/**
 * Internal passes are similar to transformation passes, but instead are called
 * programmatically. They are like utility functions, but perform in-place
 * modifications of a Configuration object. By convention, call the static run()
 * method to perform the transformation.
 * 
 * @author Stanley Bak
 */
public class DeleteParams
{
	/**
	 * Deletes param (variables / constants / labels) names from the automaton.
	 * 
	 * @param the
	 *            set of names to delete
	 */
	public static void run(Configuration config, String... names)
	{
		BaseComponent ha = (BaseComponent) config.root;

		for (String name : names)
		{
			deleteName(ha, name);

			// modify the configuration
			DeleteExpressionModifier deleter = new DeleteExpressionModifier(name);

			ExpressionModifier.modifyInitForbidden(config, deleter);

			deletePlotVariables(config, name);
		}
	}

	private static void deleteName(BaseComponent c, String name)
	{
		deleteIOName(c, name);

		deleteBaseName((BaseComponent) c, name);
	}

	private static void deleteBaseName(BaseComponent bc, String name)
	{
		DeleteExpressionModifier deleter = new DeleteExpressionModifier(name);

		// swap names in all the expressions
		ExpressionModifier.modifyBaseComponent(bc, deleter);

		// also swap left hand side of flows
		deleteFlowsLHS(bc, name);

		// also swap left hand side of resets
		deleteResetsLHS(bc, name);

		// swap the names of labels
		deleteTransitionLabels(bc, name);
	}

	private static void deleteTransitionLabels(BaseComponent bc, String name)
	{
		for (AutomatonTransition at : bc.transitions)
		{
			if (name.equals(at.label))
				at.label = null;
		}
	}

	/**
	 * Swap the names stored in the variables / constants / labels
	 * 
	 * @param c
	 *            the component to swap with
	 * @param names
	 *            the conversion map
	 */
	private static void deleteIOName(Component c, String name)
	{
		c.variables.remove(name);
		c.constants.remove(name);
		c.labels.remove(name);
	}

	private static void deletePlotVariables(Configuration config, String name)
	{
		for (int i = 0; i < 2; ++i)
		{
			if (config.settings.plotVariableNames[i].equals(name))
				config.settings.plotVariableNames[i] = config.root.variables.get(0);
		}
	}

	private static void deleteFlowsLHS(BaseComponent ha, String name)
	{
		for (AutomatonMode mode : ha.modes.values())
		{
			if (mode.urgent)
				continue;

			mode.flowDynamics.remove(name);
		}
	}

	private static void deleteResetsLHS(BaseComponent ha, String name)
	{
		for (AutomatonTransition tran : ha.transitions)
			tran.reset.remove(name);
	}

	private static class DeleteExpressionModifier extends ExpressionModifier
	{
		private String delName = null;

		public DeleteExpressionModifier(String delName)
		{
			this.delName = delName;
		}

		@Override
		protected Expression modifyExpression(Expression e)
		{
			Expression rv = e;

			if (e instanceof Variable)
			{
				Variable v = (Variable) e;

				if (v.name.equals(delName))
					throw new AutomatonExportException("Could not delete variable '" + delName
							+ "' (used in non-boolean expression)");
			}
			else if (e instanceof Operation)
			{
				Operation o = (Operation) e;

				if (Operator.isComparison(o.op))
				{
					Expression l = o.getLeft();
					Expression r = o.getRight();

					if (l instanceof Variable && ((Variable) l).name.equals(delName))
						rv = Constant.TRUE;
					else if (r instanceof Variable && ((Variable) r).name.equals(delName))
						rv = Constant.TRUE;
				}
				else
				{
					rv = new Operation(o.op);

					for (Expression child : o.children)
						rv.asOperation().children.add(modifyExpression(child));

					if (o.op == Operator.AND && rv.asOperation().getLeft() == Constant.TRUE)
						rv = o.getRight();
					else if (o.op == Operator.AND && rv.asOperation().getRight() == Constant.TRUE)
						rv = o.getLeft();
				}
			}

			return rv;
		}
	}
}
