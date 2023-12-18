package hu.bme.mit.theta.analysis.zone;

import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.expr.StmtAction;

import java.util.Collection;
import java.util.Collections;

public class ZoneStmtInvTransFunc implements InvTransFunc<ZoneState, StmtAction, ZonePrec> {

    private final static ZoneStmtInvTransFunc INSTANCE = new ZoneStmtInvTransFunc();

    private ZoneStmtInvTransFunc() {
    }

    public static ZoneStmtInvTransFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends ZoneState> getPreStates(ZoneState state, StmtAction action, ZonePrec prec) {
        return Collections.singleton(ZoneStmtApplier.pre(state, action, prec));
    }
}
