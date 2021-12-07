package hu.bme.mit.theta.analysis.zone;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.TransFunc;

public class ZoneAnalysis implements Analysis<ZoneState, ClockAction, ZonePrec> {

    private static final ZoneAnalysis INSTANCE = new ZoneAnalysis();

    private ZoneAnalysis() {
    }

    static ZoneAnalysis getInstance() {
        return INSTANCE;
    }

    @Override
    public PartialOrd<ZoneState> getPartialOrd() {
        return ZoneOrd.getInstance();
    }

    @Override
    public InitFunc<ZoneState, ZonePrec> getInitFunc() {
        return ZoneInitFunc.getInstance();
    }

    @Override
    public TransFunc<ZoneState, ClockAction, ZonePrec> getTransFunc() {
        return ZoneTransFunc.getInstance();
    }
}
