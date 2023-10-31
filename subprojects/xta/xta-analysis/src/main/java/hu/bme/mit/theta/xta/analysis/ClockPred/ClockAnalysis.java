package hu.bme.mit.theta.xta.analysis.ClockPred;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.analysis.XtaAction;

public abstract class ClockAnalysis<P extends ZonePrec> implements Analysis<ZoneState,XtaAction,P> {

    public abstract PartialOrd<ZoneState> getPartialOrd();
    public abstract InitFunc<ZoneState, P> getInitFunc();

    public abstract TransFunc<ZoneState,XtaAction,P> getTransFunc();
}
