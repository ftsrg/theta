package hu.bme.mit.theta.analysis.zone;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Concretizer;

public final class ZoneConcretizer implements Concretizer<ZoneState, ZoneState> {

    private final static ZoneConcretizer INSTANCE = new ZoneConcretizer();

    private final PartialOrd<ZoneState> ord;

    private ZoneConcretizer() {
        ord = ZoneOrd.getInstance();
    }

    public static ZoneConcretizer getInstance() {
        return INSTANCE;
    }

    @Override
    public ZoneState concretize(ZoneState state) {
        return state;
    }

    @Override
    public boolean proves(ZoneState state1, ZoneState state2) {
        return ord.isLeq(state1, state2);
    }

    @Override
    public boolean inconsistentConcrState(ZoneState state) {
        return state.isBottom();
    }
}
