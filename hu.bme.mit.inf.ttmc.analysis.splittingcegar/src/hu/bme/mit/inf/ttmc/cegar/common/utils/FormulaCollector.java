package hu.bme.mit.inf.ttmc.cegar.common.utils;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;

/**
 * Helper class that can collect atomic formulas from a system definition or an
 * expression.
 *
 * @author Akos
 */
public class FormulaCollector {

	private FormulaCollector() {
	}

	/**
	 * Collect atomic formulas from the conditions of IfThenElse expressions.
	 * The uniqueness of collection is the responsibility of the collection
	 *
	 * @param system
	 *            System
	 * @param collectTo
	 *            A collection where the formulas are collected
	 */
	public static void collectAtomsFromTransitionConditions(final STS system, final Collection<Expr<? extends BoolType>> collectTo) {
		final Collection<Expr<? extends BoolType>> conditions = new ArrayList<>();
		final ITECondCollectorVisitor collector = new ITECondCollectorVisitor();
		for (final Expr<? extends BoolType> tran : system.getTrans())
			tran.accept(collector, conditions);
		for (final Expr<? extends BoolType> cond : conditions)
			FormalismUtils.collectAtoms(cond, collectTo);
	}

	/**
	 * Collect atomic formulas from an expression. The uniqueness of collection
	 * is the responsibility of the collection
	 *
	 * @param expr
	 *            Expression
	 * @param collectTo
	 *            A collection where the formulas are collected
	 */
	public static void collectAtomsFromExpression(final Expr<? extends BoolType> expr, final Collection<Expr<? extends BoolType>> collectTo) {
		FormalismUtils.collectAtoms(expr, collectTo);
	}
}
