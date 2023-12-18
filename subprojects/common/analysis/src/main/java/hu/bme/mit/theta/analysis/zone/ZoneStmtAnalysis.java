package hu.bme.mit.theta.analysis.zone;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.StmtAction;

public class ZoneStmtAnalysis implements Analysis<ZoneState, StmtAction, ZonePrec> {

    private static final ZoneStmtAnalysis INSTANCE = new ZoneStmtAnalysis();

    private final PartialOrd<ZoneState> partialOrd;
    private final InitFunc<ZoneState, ZonePrec> initFunc;
    private final TransFunc<ZoneState, StmtAction, ZonePrec> transFunc;

    private ZoneStmtAnalysis() {
        this.partialOrd = ZoneOrd.getInstance();
        this.initFunc = ZoneInitFunc.getInstance();
        this.transFunc = ZoneStmtTransFunc.getInstance();
    }

    public static ZoneStmtAnalysis getInstance() {
        return INSTANCE;
    }

    @Override
    public PartialOrd<ZoneState> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public InitFunc<ZoneState, ZonePrec> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<ZoneState, StmtAction, ZonePrec> getTransFunc() {
        return transFunc;
    }
}
