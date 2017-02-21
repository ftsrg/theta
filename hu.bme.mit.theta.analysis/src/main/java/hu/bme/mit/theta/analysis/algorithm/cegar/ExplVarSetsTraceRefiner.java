package hu.bme.mit.theta.analysis.algorithm.cegar;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.IndexedVarsRefutation;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public class ExplVarSetsTraceRefiner<S extends ExprState, A extends ExprAction>
		implements TraceRefiner<S, A, ExplPrecision, IndexedVarsRefutation>,
		TraceSeqRefiner<S, A, ExplPrecision, IndexedVarsRefutation> {

	@Override
	public ExplPrecision refine(final Trace<S, A> trace, final ExplPrecision precision,
			final IndexedVarsRefutation refutation) {
		final Set<VarDecl<? extends Type>> vars = refutation.getVarSets().getAllVars();
		final ExplPrecision refinedPrecision = precision.refine(vars);
		return refinedPrecision;
	}

	@Override
	public List<ExplPrecision> refine(final Trace<S, A> trace, final List<ExplPrecision> precisions,
			final IndexedVarsRefutation refutation) {
		final List<ExplPrecision> refinedPrecisions = new ArrayList<>(precisions.size());
		for (int i = 0; i < precisions.size(); ++i) {
			refinedPrecisions.add(precisions.get(i).refine(refutation.getVarSets().getVars(i)));
		}
		return refinedPrecisions;
	}

}
