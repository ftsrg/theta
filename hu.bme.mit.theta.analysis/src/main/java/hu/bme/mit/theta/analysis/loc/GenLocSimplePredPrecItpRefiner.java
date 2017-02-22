package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.cegar.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public class GenLocSimplePredPrecItpRefiner<S extends State, A extends Action, L extends Loc<L, E>, E extends Edge<L, E>>
		implements PrecRefiner<LocState<S, L, E>, A, LocPrecision<SimplePredPrecision, L, E>, ItpRefutation> {

	@Override
	public LocPrecision<SimplePredPrecision, L, E> refine(final Trace<LocState<S, L, E>, A> trace,
			final LocPrecision<SimplePredPrecision, L, E> precision, final ItpRefutation refutation) {
		checkArgument(precision instanceof GenericLocPrecision); // TODO: enforce this in a better way
		final GenericLocPrecision<SimplePredPrecision, L, E> genPrecision = (GenericLocPrecision<SimplePredPrecision, L, E>) precision;
		checkArgument(trace.getStates().size() == refutation.size());
		final List<L> locs = new ArrayList<>();
		final List<SimplePredPrecision> precs = new ArrayList<>();
		for (int i = 0; i < refutation.size(); ++i) {
			final L loc = trace.getState(i).getLoc();
			final SimplePredPrecision innerPrec = genPrecision.getPrecision(loc);
			final SimplePredPrecision refinedInnerPrec = innerPrec
					.join(SimplePredPrecision.create(Collections.singleton(refutation.get(i)), innerPrec.getSolver()));
			locs.add(loc);
			precs.add(refinedInnerPrec);
		}

		return genPrecision.refine(locs, precs);
	}

}
