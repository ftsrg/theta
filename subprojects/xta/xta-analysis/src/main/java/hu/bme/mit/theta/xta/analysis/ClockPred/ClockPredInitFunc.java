package hu.bme.mit.theta.xta.analysis.ClockPred;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.zone.ClockPredPrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

import java.util.Collection;
import java.util.Collections;

import static com.google.common.base.Preconditions.checkNotNull;

public class ClockPredInitFunc implements InitFunc<ZoneState, ClockPredPrec> {


    private static ClockPredInitFunc INSTANCE = new ClockPredInitFunc();
    private ClockPredInitFunc(){}

    static ClockPredInitFunc getInstance(){ return INSTANCE;}
    @Override
    public Collection<ZoneState> getInitStates(ClockPredPrec prec)
    {
        checkNotNull(prec);
        return Collections.singleton(ZoneState.zero(prec.getVars()).transform().up().build());
    }
}
