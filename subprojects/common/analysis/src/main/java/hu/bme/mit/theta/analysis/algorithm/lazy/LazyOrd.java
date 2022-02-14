package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public final class LazyOrd<SConcr extends State, SAbstr extends ExprState> implements PartialOrd<LazyState<SConcr, SAbstr>> {

    private final PartialOrd<SAbstr> ord;

    private LazyOrd(final PartialOrd<SAbstr> ord) {
        this.ord = checkNotNull(ord);
    }

    public static <SConcr extends State, SAbstr extends ExprState> LazyOrd<SConcr, SAbstr> create(final PartialOrd<SAbstr> ord) {
        return new LazyOrd<>(ord);
    }

    @Override
    public boolean isLeq(final LazyState<SConcr, SAbstr> state1, final LazyState<SConcr, SAbstr> state2) {
        return ord.isLeq(state1.getAbstrState(), state2.getAbstrState());
    }
}
