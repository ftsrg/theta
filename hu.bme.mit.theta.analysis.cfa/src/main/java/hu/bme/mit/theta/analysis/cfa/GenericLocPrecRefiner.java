package hu.bme.mit.theta.analysis.cfa;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

public class GenericLocPrecRefiner<S extends State, A extends Action, P extends Prec, R extends Refutation>
		implements PrecRefiner<LocState<S>, A, LocPrec<P>, R> {

	private final RefutationToPrec<P, R> refToPrec;

	private GenericLocPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
		this.refToPrec = checkNotNull(refToPrec);
	}

	public static <S extends State, A extends Action, P extends Prec, R extends Refutation> GenericLocPrecRefiner<S, A, P, R> create(
			final RefutationToPrec<P, R> refToPrec) {
		return new GenericLocPrecRefiner<>(refToPrec);
	}

	@Override
	public LocPrec<P> refine(final LocPrec<P> prec, final Trace<LocState<S>, A> trace, final R refutation) {
		checkNotNull(trace);
		checkNotNull(prec);
		checkNotNull(refutation);
		checkArgument(prec instanceof GenericLocPrec); // TODO: enforce this in a better way

		final GenericLocPrec<P> genPrec = (GenericLocPrec<P>) prec;
		final Map<Loc, P> runningPrecs = new HashMap<>();
		for (final LocState<S> state : trace.getStates()) {
			runningPrecs.put(state.getLoc(), genPrec.getPrec(state.getLoc()));
		}

		for (int i = 0; i < trace.getStates().size(); ++i) {
			final Loc loc = trace.getState(i).getLoc();
			final P precForLoc = runningPrecs.get(loc);
			final P newPrecForLoc = refToPrec.toPrec(refutation, i);
			runningPrecs.put(loc, refToPrec.join(precForLoc, newPrecForLoc));
		}

		return genPrec.refine(runningPrecs);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
