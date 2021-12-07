package hu.bme.mit.theta.analysis.zone;

import hu.bme.mit.theta.analysis.TransFunc;

import java.util.Collection;
import java.util.Collections;

public class ZoneTransFunc implements TransFunc<ZoneState, ClockAction, ZonePrec> {

    private static final ZoneTransFunc INSTANCE = new ZoneTransFunc();

    private ZoneTransFunc() {
    }

    static ZoneTransFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends ZoneState> getSuccStates(ZoneState state, ClockAction action, ZonePrec prec) {
        ZoneState.Builder builder = state.transform();
        action.getClockOps().forEach(builder::execute);
        ZoneState succState = builder.build();
        return Collections.singleton(succState);
    }
}
