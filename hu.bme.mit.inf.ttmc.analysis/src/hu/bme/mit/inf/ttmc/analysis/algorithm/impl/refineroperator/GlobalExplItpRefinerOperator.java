package hu.bme.mit.inf.ttmc.analysis.algorithm.impl.refineroperator;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.RefinerOperator;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.expl.GlobalExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.refutation.ItpRefutation;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismUtils;

public class GlobalExplItpRefinerOperator<A extends Action> implements RefinerOperator<ExplState, A, ItpRefutation, GlobalExplPrecision> {

	@Override
	public GlobalExplPrecision refine(final GlobalExplPrecision precision, final ItpRefutation refutation, final Counterexample<ExplState, A> counterexample) {
		final Set<VarDecl<? extends Type>> newVisiblevars = new HashSet<>();
		for (final Expr<? extends BoolType> pred : refutation) {
			FormalismUtils.collectVars(pred, newVisiblevars);
		}
		return precision.refine(newVisiblevars);
	}

}
