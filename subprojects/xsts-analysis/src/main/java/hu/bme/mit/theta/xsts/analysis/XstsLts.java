package hu.bme.mit.theta.xsts.analysis;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Collection;
import java.util.stream.Collectors;

public class XstsLts implements LTS<XstsState, XstsAction> {

    private final Collection<XstsAction> internalActions;
    private final Collection<XstsAction> externalActions;

    private XstsLts(final XSTS xsts){
        internalActions=xsts.getTransitions().getStmts().stream().map(XstsAction::create).collect(Collectors.toList());
        externalActions=ImmutableList.of(XstsAction.create(xsts.getEnvAction()));
    }

    public static LTS<XstsState, XstsAction> create(final XSTS xsts){
        return new XstsLts(xsts);
    }

    @Override
    public Collection<XstsAction> getEnabledActionsFor(XstsState state) {
        if(state.isLastActionWasEnv()) return internalActions;
        else return externalActions;
    }
}
