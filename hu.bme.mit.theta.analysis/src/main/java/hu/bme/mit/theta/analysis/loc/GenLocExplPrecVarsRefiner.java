package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.cegar.PrecRefiner;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expr.IndexedVarsRefutation;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public class GenLocExplPrecVarsRefiner<S extends State, A extends Action, L extends Loc<L, E>, E extends Edge<L, E>>
		implements PrecRefiner<LocState<S, L, E>, A, LocPrecision<ExplPrecision, L, E>, IndexedVarsRefutation> {

	@Override
	public LocPrecision<ExplPrecision, L, E> refine(final Trace<LocState<S, L, E>, A> trace,
			final LocPrecision<ExplPrecision, L, E> precision, final IndexedVarsRefutation refutation) {
		checkArgument(precision instanceof GenericLocPrecision); // TODO: enforce this in a better way
		final GenericLocPrecision<ExplPrecision, L, E> genPrecision = (GenericLocPrecision<ExplPrecision, L, E>) precision;
		final List<L> locs = new ArrayList<>();
		final List<ExplPrecision> precs = new ArrayList<>();
		for (int i = 0; i < trace.getStates().size(); ++i) {
			final L loc = trace.getState(i).getLoc();
			final ExplPrecision innerPrec = genPrecision.getPrecision(loc);
			final ExplPrecision refinedInnerPrec = innerPrec
					.join(ExplPrecision.create(refutation.getVarSets().getVars(i)));
			locs.add(loc);
			precs.add(refinedInnerPrec);
		}

		return genPrecision.refine(locs, precs);
	}

}
