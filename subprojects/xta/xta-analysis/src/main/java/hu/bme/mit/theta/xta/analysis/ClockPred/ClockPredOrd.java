package hu.bme.mit.theta.xta.analysis.ClockPred;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.zone.ZoneState;

public class ClockPredOrd implements PartialOrd<ClockPredState> {


    @Override
    public boolean isLeq(ClockPredState state1, ClockPredState state2) {
        return state1.isLeq(state2);
    }
}
