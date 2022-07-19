package hu.bme.mit.theta.xta.analysis.zone;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.analysis.XtaAction;

import java.util.Collection;

public final class XtaZoneInvTransFunc implements InvTransFunc<ZoneState, XtaAction, ZonePrec> {

    private final static XtaZoneInvTransFunc INSTANCE = new XtaZoneInvTransFunc();

    private XtaZoneInvTransFunc() { }

    public static XtaZoneInvTransFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends ZoneState> getPreStates(ZoneState state, XtaAction action, ZonePrec prec) {
        final ZoneState preState = XtaZoneUtils.pre(state, action, prec);
        return ImmutableList.of(preState);
    }
}
