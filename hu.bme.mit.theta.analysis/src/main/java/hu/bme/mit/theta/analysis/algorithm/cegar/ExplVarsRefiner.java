package hu.bme.mit.theta.analysis.algorithm.cegar;

import java.util.Collection;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableList.Builder;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PrecTrace;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expr.IndexedVarsRefutation;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public class ExplVarsRefiner<S extends State, A extends Action>
		implements PrecRefiner<S, A, ExplPrec, IndexedVarsRefutation>,
		PrecTraceRefiner<S, A, ExplPrec, IndexedVarsRefutation> {

	@Override
	public ExplPrec refine(final Trace<S, A> trace, final ExplPrec prec,
			final IndexedVarsRefutation refutation) {
		final Collection<VarDecl<? extends Type>> vars = refutation.getVarSets().getAllVars();
		final ExplPrec refinedPrec = prec.join(ExplPrec.create(vars));
		return refinedPrec;
	}

	@Override
	public PrecTrace<S, A, ExplPrec> refine(final PrecTrace<S, A, ExplPrec> trace,
			final IndexedVarsRefutation refutation) {
		final Builder<ExplPrec> builder = ImmutableList.builder();
		for (int i = 0; i < trace.getPrecs().size(); ++i) {
			final Collection<VarDecl<? extends Type>> vars = refutation.getVarSets().getVars(i);
			final ExplPrec refinedPrec = trace.getPrec(i).join(ExplPrec.create(vars));
			builder.add(refinedPrec);
		}
		return PrecTrace.of(trace.getTrace(), builder.build());
	}

}
