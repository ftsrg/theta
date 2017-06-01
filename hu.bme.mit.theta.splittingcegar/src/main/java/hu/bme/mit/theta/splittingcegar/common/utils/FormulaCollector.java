package hu.bme.mit.theta.splittingcegar.common.utils;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.formalism.sts.STS;

public final class FormulaCollector {

	private FormulaCollector() {
	}

	public static void collectAtomsFromTransitionConditions(final STS sts, final Collection<Expr<BoolType>> collectTo) {
		final Collection<Expr<BoolType>> conditions = new ArrayList<>();
		IteCondCollector.collectIteConds(sts.getTrans(), collectTo);
		for (final Expr<BoolType> cond : conditions)
			ExprUtils.collectAtoms(cond, collectTo);
	}

	public static void collectAtomsFromExpression(final Expr<BoolType> expr,
			final Collection<Expr<BoolType>> collectTo) {
		ExprUtils.collectAtoms(expr, collectTo);
	}
}
