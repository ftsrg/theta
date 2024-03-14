package hu.bme.mit.theta.xta.analysis.ClockPred;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.zone.*;
import hu.bme.mit.theta.xta.analysis.XtaAction;

import java.time.Clock;

public class ClockPredAnalysis implements Analysis<ZoneState,XtaAction,ClockPredPrec> {

    private final InitFunc<ZoneState, ClockPredPrec> initFunc;

    private ClockPredAnalysis(DBM initDBM){
        this.initFunc = ClockPredInitFunc.create(initDBM);
    }
    public static ClockPredAnalysis create(DBM initDBM){return new ClockPredAnalysis(initDBM);}
    @Override
    public PartialOrd<ZoneState> getPartialOrd() {
        return ZoneOrd.getInstance();
    }

    @Override
    public InitFunc<ZoneState, ClockPredPrec> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<ZoneState, XtaAction, ClockPredPrec> getTransFunc() {
        return ClockPredTransFunc.getInstance();
    }
}
