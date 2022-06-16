package hu.bme.mit.theta.analysis.itp;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public final class ItpOrd<SConcr extends State, SAbstr extends ExprState> implements PartialOrd<ItpState<SConcr, SAbstr>> {

    private final PartialOrd<SAbstr> ord;

    private ItpOrd(final PartialOrd<SAbstr> ord) {
        this.ord = checkNotNull(ord);
    }

    public static <SConcr extends State, SAbstr extends ExprState> ItpOrd<SConcr, SAbstr> create(final PartialOrd<SAbstr> ord) {
        return new ItpOrd<>(ord);
    }

    @Override
    public boolean isLeq(final ItpState<SConcr, SAbstr> state1, final ItpState<SConcr, SAbstr> state2) {
        return ord.isLeq(state1.getAbstrState(), state2.getAbstrState());
    }
}
