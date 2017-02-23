package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableList.Builder;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PrecTrace;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public class SimplePredItpRefiner<S extends State, A extends Action>
		implements PrecRefiner<S, A, SimplePredPrec, ItpRefutation>,
		PrecTraceRefiner<S, A, SimplePredPrec, ItpRefutation> {

	@Override
	public SimplePredPrec refine(final Trace<S, A> trace, final SimplePredPrec precision,
			final ItpRefutation refutation) {
		final SimplePredPrec refinedPrecision = precision
				.join(SimplePredPrec.create(refutation, precision.getSolver()));
		return refinedPrecision;
	}

	@Override
	public PrecTrace<S, A, SimplePredPrec> refine(final PrecTrace<S, A, SimplePredPrec> trace,
			final ItpRefutation refutation) {
		checkArgument(trace.getPrecs().size() == refutation.size());
		final Builder<SimplePredPrec> builder = ImmutableList.builder();
		for (int i = 0; i < trace.getPrecs().size(); ++i) {
			final Expr<? extends BoolType> expr = refutation.get(i);
			final SimplePredPrec prec = trace.getPrec(i);
			final SimplePredPrec refinedPrec = prec.join(SimplePredPrec.create(expr, prec.getSolver()));
			builder.add(refinedPrec);
		}
		return PrecTrace.of(trace.getTrace(), builder.build());
	}
}
