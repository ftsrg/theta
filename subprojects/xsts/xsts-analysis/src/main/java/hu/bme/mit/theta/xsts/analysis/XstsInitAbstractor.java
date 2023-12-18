package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XstsInitAbstractor<SConcr extends ExprState, SAbstr extends ExprState>
        implements InitAbstractor<XstsState<SConcr>, XstsState<SAbstr>> {

    private final InitAbstractor<SConcr, SAbstr> initAbstractor;

    private XstsInitAbstractor(final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        this.initAbstractor = checkNotNull(initAbstractor);
    }

    public static <SConcr extends ExprState, SAbstr extends ExprState> XstsInitAbstractor<SConcr, SAbstr>
    create(final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        return new XstsInitAbstractor<>(initAbstractor);
    }

    @Override
    public XstsState<SAbstr> getInitAbstrState(XstsState<SConcr> concrXstsState) {
        final SConcr concrState = concrXstsState.getState();
        final SAbstr abstrState = initAbstractor.getInitAbstrState(concrState);
        final boolean lastActionWasEnv = concrXstsState.lastActionWasEnv();
        final boolean isInitialized = concrXstsState.isInitialized();
        final XstsState<SAbstr> abstrXstsState = XstsState.of(abstrState, lastActionWasEnv, isInitialized);
        return abstrXstsState;
    }
}
