package hu.bme.mit.inf.ttmc.analysis.algorithm.impl.refinerops;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Trace;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.RefinerOp;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.expl.GlobalExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.refutation.ItpRefutation;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismUtils;

public class GlobalExplItpRefinerOp<A extends Action> implements RefinerOp<ExplState, A, ItpRefutation, GlobalExplPrecision> {

	@Override
	public GlobalExplPrecision refine(final GlobalExplPrecision precision, final ItpRefutation refutation, final Trace<ExplState, A> counterexample) {
		final Set<VarDecl<? extends Type>> newVisibleVars = new HashSet<>();
		for (final Expr<? extends BoolType> pred : refutation) {
			FormalismUtils.collectVars(pred, newVisibleVars);
		}
		return precision.with(newVisibleVars);
	}

}
