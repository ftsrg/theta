package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableList.Builder;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PrecTrace;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

public class ExplItpRefiner<S extends State, A extends Action> implements
		PrecRefiner<S, A, ExplPrecision, ItpRefutation>, PrecTraceRefiner<S, A, ExplPrecision, ItpRefutation> {

	@Override
	public ExplPrecision refine(final Trace<S, A> trace, final ExplPrecision precision,
			final ItpRefutation refutation) {
		final Collection<VarDecl<? extends Type>> vars = ExprUtils.getVars(refutation);
		final ExplPrecision refinedPrecision = precision.join(ExplPrecision.create(vars));
		return refinedPrecision;
	}

	@Override
	public PrecTrace<S, A, ExplPrecision> refine(final PrecTrace<S, A, ExplPrecision> trace,
			final ItpRefutation refutation) {
		checkArgument(trace.getPrecs().size() == refutation.size());
		final Builder<ExplPrecision> builder = ImmutableList.builder();
		for (int i = 0; i < trace.getPrecs().size(); ++i) {
			final Collection<VarDecl<? extends Type>> vars = ExprUtils.getVars(refutation.get(i));
			final ExplPrecision refinedPrec = trace.getPrec(i).join(ExplPrecision.create(vars));
			builder.add(refinedPrec);
		}
		return PrecTrace.of(trace.getTrace(), builder.build());
	}
}
