package hu.bme.mit.theta.xta.analysis.ClockPred;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.zone.ClockPredPrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.analysis.XtaAction;


import java.util.Collection;

public class ClockPredTransFunc implements TransFunc<ZoneState, XtaAction, ClockPredPrec> {

    private final static ClockPredTransFunc INSTANCE = new ClockPredTransFunc();
    private ClockPredTransFunc(){}

    static ClockPredTransFunc getInstance(){return INSTANCE;}
    public Collection<? extends ZoneState> getSuccStates(ZoneState state, XtaAction action, ClockPredPrec prec) {

        ZoneState succState = XtaClockPredUtils.post(state, action, prec);
        if(!succState.isBottom() && prec.getShouldApplyPredicates()){
            succState.clockPredicate(prec);
        }
        return ImmutableList.of(succState);
    }
}
