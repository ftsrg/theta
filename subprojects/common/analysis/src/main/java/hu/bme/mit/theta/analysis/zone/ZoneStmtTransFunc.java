package hu.bme.mit.theta.analysis.zone;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.StmtAction;

import java.util.Collection;
import java.util.Collections;

public class ZoneStmtTransFunc implements TransFunc<ZoneState, StmtAction, ZonePrec> {

    private final static ZoneStmtTransFunc INSTANCE = new ZoneStmtTransFunc();

    private ZoneStmtTransFunc() {
    }

    public static ZoneStmtTransFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends ZoneState> getSuccStates(ZoneState state, StmtAction action, ZonePrec prec) {
        return Collections.singleton(ZoneStmtApplier.post(state, action, prec));
    }
}
