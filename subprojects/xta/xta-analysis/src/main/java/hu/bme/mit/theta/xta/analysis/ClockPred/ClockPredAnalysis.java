package hu.bme.mit.theta.xta.analysis.ClockPred;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.zone.ClockPredPrec;
import hu.bme.mit.theta.analysis.zone.ZoneOrd;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.analysis.XtaAction;

import java.time.Clock;

public class ClockPredAnalysis implements Analysis<ZoneState,XtaAction,ClockPredPrec> {

    private static final ClockPredAnalysis INSTANCE = new ClockPredAnalysis();

    private ClockPredAnalysis(){

    }
    public static ClockPredAnalysis getInstance(){return INSTANCE;}
    @Override
    public PartialOrd<ZoneState> getPartialOrd() {
        return ZoneOrd.getInstance();
    }

    @Override
    public InitFunc<ZoneState, ClockPredPrec> getInitFunc() {
        return ClockPredInitFunc.getInstance();
    }

    @Override
    public TransFunc<ZoneState, XtaAction, ClockPredPrec> getTransFunc() {
        return ClockPredTransFunc.getInstance();
    }
}
