package hu.bme.mit.theta.analysis.algorithm.impl.refinerops;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.impl.RefinerOp;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.refutation.ItpRefutation;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

public class GlobalExplItpRefinerOp<A extends Action>
		implements RefinerOp<ExplState, A, ItpRefutation, ExplPrecision> {

	@Override
	public ExplPrecision refine(final ExplPrecision precision, final ItpRefutation refutation,
			final Trace<ExplState, A> counterexample) {
		final Set<VarDecl<? extends Type>> newVisibleVars = new HashSet<>();
		for (final Expr<? extends BoolType> pred : refutation) {
			ExprUtils.collectVars(pred, newVisibleVars);
		}
		return precision.with(newVisibleVars);
	}

}
