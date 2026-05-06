package hu.bme.mit.theta.analysis.algorithm.lazy.itp;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;

import static com.google.common.base.Preconditions.checkNotNull;

public final class BasicConcretizer<S extends State> implements Concretizer<S, S> {

    private final PartialOrd<S> ord;

    private BasicConcretizer(final PartialOrd<S> ord) {
        this.ord = checkNotNull(ord);
    }

    public static <S extends State> BasicConcretizer<S> create(final PartialOrd<S> ord) {
        return new BasicConcretizer<S>(ord);
    }

    @Override
    public final S concretize(final S state) {
        return state;
    }

    @Override
    public boolean proves(final S state1, final S state2) {
        return ord.isLeq(state1, state2);
    }

    @Override
    public boolean inconsistentConcrState(S state) {
        return state.isBottom();
    }
}
