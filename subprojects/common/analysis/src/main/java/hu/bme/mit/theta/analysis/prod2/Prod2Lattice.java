package hu.bme.mit.theta.analysis.prod2;

import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;

import static com.google.common.base.Preconditions.checkNotNull;

public final class Prod2Lattice<S1 extends State, S2 extends State> implements Lattice<Prod2State<S1, S2>> {

    private final Lattice<S1> lattice1;
    private final Lattice<S2> lattice2;

    private Prod2Lattice(final Lattice<S1> lattice1, final Lattice<S2> lattice2) {
        this.lattice1 = checkNotNull(lattice1);
        this.lattice2 = checkNotNull(lattice2);
    }

    public static <S1 extends State, S2 extends State> Prod2Lattice<S1, S2> create(final Lattice<S1> lattice1, final Lattice<S2> lattice2) {
        return new Prod2Lattice<>(lattice1, lattice2);
    }

    @Override
    public Prod2State<S1, S2> top() {
        return Prod2State.of(lattice1.top(), lattice2.top());
    }

    @Override
    public Prod2State<S1, S2> bottom() {
        return Prod2State.of(lattice1.bottom(), lattice2.bottom());
    }

    @Override
    public Prod2State<S1, S2> meet(Prod2State<S1, S2> state1, Prod2State<S1, S2> state2) {
        return Prod2State.of(lattice1.meet(state1.getState1(), state2.getState1()), lattice2.meet(state1.getState2(), state2.getState2()));
    }

    @Override
    public Prod2State<S1, S2> join(Prod2State<S1, S2> state1, Prod2State<S1, S2> state2) {
        return Prod2State.of(lattice1.join(state1.getState1(), state2.getState1()), lattice2.join(state1.getState2(), state2.getState2()));
    }

    @Override
    public boolean isLeq(Prod2State<S1, S2> state1, Prod2State<S1, S2> state2) {
        return lattice1.isLeq(state1.getState1(), state2.getState1()) && lattice2.isLeq(state1.getState2(), state2.getState2());
    }
}
