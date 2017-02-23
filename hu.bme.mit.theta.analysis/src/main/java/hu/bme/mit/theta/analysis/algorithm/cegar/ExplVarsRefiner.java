package hu.bme.mit.theta.analysis.algorithm.cegar;

import java.util.Collection;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableList.Builder;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PrecTrace;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expr.IndexedVarsRefutation;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public class ExplVarsRefiner<S extends State, A extends Action>
		implements PrecRefiner<S, A, ExplPrecision, IndexedVarsRefutation>,
		PrecTraceRefiner<S, A, ExplPrecision, IndexedVarsRefutation> {

	@Override
	public ExplPrecision refine(final Trace<S, A> trace, final ExplPrecision precision,
			final IndexedVarsRefutation refutation) {
		final Collection<VarDecl<? extends Type>> vars = refutation.getVarSets().getAllVars();
		final ExplPrecision refinedPrecision = precision.join(ExplPrecision.create(vars));
		return refinedPrecision;
	}

	@Override
	public PrecTrace<S, A, ExplPrecision> refine(final PrecTrace<S, A, ExplPrecision> trace,
			final IndexedVarsRefutation refutation) {
		final Builder<ExplPrecision> builder = ImmutableList.builder();
		for (int i = 0; i < trace.getPrecs().size(); ++i) {
			final Collection<VarDecl<? extends Type>> vars = refutation.getVarSets().getVars(i);
			final ExplPrecision refinedPrec = trace.getPrec(i).join(ExplPrecision.create(vars));
			builder.add(refinedPrec);
		}
		return PrecTrace.of(trace.getTrace(), builder.build());
	}

}
