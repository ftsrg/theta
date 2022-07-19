package hu.bme.mit.theta.xcfa.analysis.impl.lazy;

import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;
import hu.bme.mit.theta.xcfa.analysis.impl.singlethread.XcfaSTState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.function.BiFunction;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XcfaInitAbstractor<SConcr extends ExprState, SAbstr extends ExprState> implements InitAbstractor<XcfaState<SConcr>, XcfaState<SAbstr>> {

    private final InitAbstractor<SConcr, SAbstr> initAbstractor;
    private final BiFunction<XcfaLocation, SAbstr, XcfaState<SAbstr>> abstractStateCreator;

    private XcfaInitAbstractor(final InitAbstractor<SConcr, SAbstr> initAbstractor,
                               final BiFunction<XcfaLocation, SAbstr, XcfaState<SAbstr>> abstractStateCreator) {
        this.initAbstractor = checkNotNull(initAbstractor);
        this.abstractStateCreator = abstractStateCreator;
    }

    public static <SConcr extends ExprState, SAbstr extends ExprState> XcfaInitAbstractor<SConcr, SAbstr>
    create(final InitAbstractor<SConcr, SAbstr> initAbstractor,
           final BiFunction<XcfaLocation, SAbstr, XcfaState<SAbstr>> abstractStateCreator) {
        return new XcfaInitAbstractor<>(initAbstractor, abstractStateCreator);
    }

    @Override
    public XcfaState<SAbstr> getInitAbstrState(final XcfaState<SConcr> state) {
        final XcfaLocation locs = state.getCurrentLoc();
        final SConcr concrState = state.getGlobalState();
        final SAbstr abstrState = initAbstractor.getInitAbstrState(concrState);
        return abstractStateCreator.apply(locs, abstrState);
        // return XcfaSTState.create(locs, abstrState);
    }
}
