package hu.bme.mit.theta.xcfa.analysis.impl.lazy;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;
import hu.bme.mit.theta.xcfa.analysis.impl.singlethread.XcfaSTState;

public final class XcfaLensUtils {

    public static <DConcr extends ExprState, DAbstr extends ExprState> Lens<LazyState<XcfaState<DConcr>, XcfaState<DAbstr>>, LazyState<DConcr, DAbstr>>
    createLazyDataLens() {
        final Lens<LazyState<XcfaState<DConcr>, XcfaState<DAbstr>>, DConcr> concrLens = createConcrDataLens();
        final Lens<LazyState<XcfaState<DConcr>, XcfaState<DAbstr>>, DAbstr> abstrLens = createAbstrDataLens();
        return new Lens<>() {
            @Override
            public LazyState<DConcr, DAbstr> get(LazyState<XcfaState<DConcr>, XcfaState<DAbstr>> state) {
                final DConcr concrState = concrLens.get(state);
                if (concrState.isBottom()) {
                    return LazyState.bottom(concrState);
                } else {
                    final DAbstr abstrState = abstrLens.get(state);
                    return LazyState.of(concrState, abstrState);
                }
            }
            @Override
            public LazyState<XcfaState<DConcr>, XcfaState<DAbstr>> set(
                    LazyState<XcfaState<DConcr>, XcfaState<DAbstr>> lazyState,
                    LazyState<DConcr, DAbstr> newItpDataState) {
                final XcfaState<DConcr> newConcrState = concrLens.set(lazyState, newItpDataState.getConcrState()).getConcrState();
                final XcfaState<DAbstr> newAbstrState = abstrLens.set(lazyState, newItpDataState.getAbstrState()).getAbstrState();
                return LazyState.of(newConcrState, newAbstrState);
            }
        };
    }

    public static <DConcr extends ExprState, DAbstr extends ExprState> Lens<LazyState<XcfaState<DConcr>, XcfaState<DAbstr>>, DConcr>
    createConcrDataLens() {
        return new Lens<>() {
            @Override
            public DConcr get(LazyState<XcfaState<DConcr>, XcfaState<DAbstr>> state) {
                return state.getConcrState().getGlobalState();
            }
            @Override
            public LazyState<XcfaState<DConcr>, XcfaState<DAbstr>> set(
                    LazyState<XcfaState<DConcr>, XcfaState<DAbstr>> lazyState,
                    DConcr newConcrDataState) {
                final XcfaState<DConcr> concrXcfaState = lazyState.getConcrState();
                final XcfaState<DConcr> newConcrXcfaState = XcfaSTState.create(concrXcfaState.getCurrentLoc(), newConcrDataState);
                return lazyState.withConcrState(newConcrXcfaState);
            }
        };
    }

    public static <DConcr extends ExprState, DAbstr extends ExprState> Lens<LazyState<XcfaState<DConcr>, XcfaState<DAbstr>>, DAbstr>
    createAbstrDataLens() {
        return new Lens<>() {
            @Override
            public DAbstr get(LazyState<XcfaState<DConcr>, XcfaState<DAbstr>> state) {
                return state.getAbstrState().getGlobalState();
            }
            @Override
            public LazyState<XcfaState<DConcr>, XcfaState<DAbstr>> set(
                    LazyState<XcfaState<DConcr>, XcfaState<DAbstr>> lazyState,
                    DAbstr newAbstrDataState) {
                final XcfaState<DAbstr> abstrXcfaState = lazyState.getAbstrState();
                final XcfaState<DAbstr> newAbstrXcfaState = XcfaSTState.create(abstrXcfaState.getCurrentLoc(), newAbstrDataState);
                return lazyState.withAbstrState(newAbstrXcfaState);
            }
        };
    }
}
