package hu.bme.mit.inf.ttmc.cegar.common.utils;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;

public class FormulaCollector {

	private FormulaCollector() {
	}

	public static void collectAtomsFromTransitionConditions(final STS sts, final Collection<Expr<? extends BoolType>> collectTo) {
		final Collection<Expr<? extends BoolType>> conditions = new ArrayList<>();
		final ITECondCollectorVisitor collector = new ITECondCollectorVisitor();
		for (final Expr<? extends BoolType> tran : sts.getTrans())
			tran.accept(collector, conditions);
		for (final Expr<? extends BoolType> cond : conditions)
			FormalismUtils.collectAtoms(cond, collectTo);
	}

	public static void collectAtomsFromExpression(final Expr<? extends BoolType> expr, final Collection<Expr<? extends BoolType>> collectTo) {
		FormalismUtils.collectAtoms(expr, collectTo);
	}
}
