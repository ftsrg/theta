package hu.bme.mit.theta.xta.analysis;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor;
import hu.bme.mit.theta.xta.XtaProcess;

import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XtaInitAbstractor<SConcr extends State, SAbstr extends State> implements InitAbstractor<XtaState<SConcr>, XtaState<SAbstr>> {

    private final InitAbstractor<SConcr, SAbstr> initAbstractor;

    private XtaInitAbstractor(final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        this.initAbstractor = checkNotNull(initAbstractor);
    }

    public static <SConcr extends State, SAbstr extends State> XtaInitAbstractor<SConcr, SAbstr>
    create(final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        return new XtaInitAbstractor<>(initAbstractor);
    }

    @Override
    public XtaState<SAbstr> getInitAbstrState(final XtaState<SConcr> state) {
        final List<XtaProcess.Loc> locs = state.getLocs();
        final SConcr concrState = state.getState();
        final SAbstr abstrState = initAbstractor.getInitAbstrState(concrState);
        return XtaState.of(locs, abstrState);
    }
}
