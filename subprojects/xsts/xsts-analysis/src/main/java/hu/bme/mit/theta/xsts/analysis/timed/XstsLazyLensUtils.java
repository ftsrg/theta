package hu.bme.mit.theta.xsts.analysis.timed;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.xsts.analysis.XstsState;

public final class XstsLazyLensUtils {

    public static <DConcr extends State, DAbstr extends ExprState> Lens<LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>>, LazyState<DConcr, DAbstr>>
    createLazyDataLens() {
        final Lens<LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>>, DConcr> concrLens = createConcrDataLens();
        final Lens<LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>>, DAbstr> abstrLens = createAbstrDataLens();
        return new Lens<>() {
            @Override
            public LazyState<DConcr, DAbstr> get(LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>> state) {
                final DConcr concrState = concrLens.get(state);
                if (concrState.isBottom()) {
                    return LazyState.bottom(concrState);
                } else {
                    final DAbstr abstrState = abstrLens.get(state);
                    return LazyState.of(concrState, abstrState);
                }
            }
            @Override
            public LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>> set(
                    LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>> lazyState,
                    LazyState<DConcr, DAbstr> newItpDataState) {
                final XstsState<Prod2State<DConcr, ?>> newConcrState = concrLens.set(lazyState, newItpDataState.getConcrState()).getConcrState();
                final XstsState<Prod2State<DAbstr, ?>> newAbstrState = abstrLens.set(lazyState, newItpDataState.getAbstrState()).getAbstrState();
                return LazyState.of(newConcrState, newAbstrState);
            }
        };
    }

    public static <CConcr extends State, CAbstr extends ExprState> Lens<LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>>, LazyState<CConcr, CAbstr>>
    createLazyClockLens() {
        final Lens<LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>>, CConcr> concrLens = createConcrClockLens();
        final Lens<LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>>, CAbstr> abstrLens = createAbstrClockLens();
        return new Lens<>() {
            @Override
            public LazyState<CConcr, CAbstr> get(LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>> state) {
                final CConcr concrState = concrLens.get(state);
                if (concrState.isBottom()) {
                    return LazyState.bottom(concrState);
                } else {
                    final CAbstr abstrState = abstrLens.get(state);
                    return LazyState.of(concrState, abstrState);
                }
            }
            @Override
            public LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>> set(
                    LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>> lazyState,
                    LazyState<CConcr, CAbstr> newItpDataState) {
                final XstsState<Prod2State<?, CConcr>> newConcrState = concrLens.set(lazyState, newItpDataState.getConcrState()).getConcrState();
                final XstsState<Prod2State<?, CAbstr>> newAbstrState = abstrLens.set(lazyState, newItpDataState.getAbstrState()).getAbstrState();
                return LazyState.of(newConcrState, newAbstrState);
            }
        };
    }

    public static <DConcr extends State, DAbstr extends State> Lens<LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>>, DConcr>
    createConcrDataLens() {
        return new Lens<>() {
            @Override
            public DConcr get(LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>> state) {
                return state.getConcrState().getState().getState1();
            }
            @Override
            public LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>> set(
                    LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>> lazyState,
                    DConcr newConcrDataState) {
                final XstsState<Prod2State<DConcr, ?>> concrXstsState = lazyState.getConcrState();
                final Prod2State<DConcr, ?> concrState = concrXstsState.getState();
                final Prod2State<DConcr, ?> newConcrState = concrState.with1(newConcrDataState);
                final XstsState<Prod2State<DConcr, ?>> newConcrXstsState =
                    XstsState.of(newConcrState, concrXstsState.lastActionWasEnv(), concrXstsState.isInitialized());
                return lazyState.withConcrState(newConcrXstsState);
            }
        };
    }

    public static <DConcr extends State, DAbstr extends State> Lens<LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>>, DAbstr>
    createAbstrDataLens() {
        return new Lens<>() {
            @Override
            public DAbstr get(LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>> state) {
                return state.getAbstrState().getState().getState1();
            }
            @Override
            public LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>> set(
                    LazyState<XstsState<Prod2State<DConcr, ?>>, XstsState<Prod2State<DAbstr, ?>>> lazyState,
                    DAbstr newAbstrDataState) {
                final XstsState<Prod2State<DAbstr, ?>> abstrXstsState = lazyState.getAbstrState();
                final Prod2State<DAbstr, ?> abstrState = abstrXstsState.getState();
                final Prod2State<DAbstr, ?> newAbstrState = abstrState.with1(newAbstrDataState);
                final XstsState<Prod2State<DAbstr, ?>> newAbstrXstsState =
                    XstsState.of(newAbstrState, abstrXstsState.lastActionWasEnv(), abstrXstsState.isInitialized());
                return lazyState.withAbstrState(newAbstrXstsState);
            }
        };
    }

    public static <CConcr extends State, CAbstr extends State> Lens<LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>>, CConcr>
    createConcrClockLens() {
        return new Lens<>() {
            @Override
            public CConcr get(LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>> state) {
                return state.getConcrState().getState().getState2();
            }
            @Override
            public LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>> set(
                    LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>> lazyState,
                    CConcr newConcrClockState) {
                final XstsState<Prod2State<?, CConcr>> concrXstsState = lazyState.getConcrState();
                final Prod2State<?, CConcr> concrState = concrXstsState.getState();
                final Prod2State<?, CConcr> newConcrState = concrState.with2(newConcrClockState);
                final XstsState<Prod2State<?, CConcr>> newConcrXstsState =
                    XstsState.of(newConcrState, concrXstsState.lastActionWasEnv(), concrXstsState.isInitialized());
                return lazyState.withConcrState(newConcrXstsState);
            }
        };
    }

    public static <CConcr extends State, CAbstr extends State> Lens<LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>>, CAbstr>
    createAbstrClockLens() {
        return new Lens<>() {
            @Override
            public CAbstr get(LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>> state) {
                return state.getAbstrState().getState().getState2();
            }
            @Override
            public LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>> set(
                    LazyState<XstsState<Prod2State<?, CConcr>>, XstsState<Prod2State<?, CAbstr>>> lazyState,
                    CAbstr newAbstrClockState) {
                final XstsState<Prod2State<?, CAbstr>> abstrXstsState = lazyState.getAbstrState();
                final Prod2State<?, CAbstr> abstrState = abstrXstsState.getState();
                final Prod2State<?, CAbstr> newAbstrState = abstrState.with2(newAbstrClockState);
                final XstsState<Prod2State<?, CAbstr>> newAbstrXstsState =
                    XstsState.of(newAbstrState, abstrXstsState.lastActionWasEnv(), abstrXstsState.isInitialized());
                return lazyState.withAbstrState(newAbstrXstsState);
            }
        };
    }

    public static <DConcr extends State, CConcr extends State, DAbstr extends State, CAbstr extends State> Lens<LazyState<XstsState<Prod2State<DConcr, CConcr>>, XstsState<Prod2State<DAbstr, CAbstr>>>, Prod2State<DConcr, CConcr>>
    createConcrProd2Lens() {
        return new Lens<>() {
            @Override
            public Prod2State<DConcr, CConcr> get(LazyState<XstsState<Prod2State<DConcr, CConcr>>, XstsState<Prod2State<DAbstr, CAbstr>>> state) {
                return state.getConcrState().getState();
            }
            @Override
            public LazyState<XstsState<Prod2State<DConcr, CConcr>>, XstsState<Prod2State<DAbstr, CAbstr>>> set(
                    LazyState<XstsState<Prod2State<DConcr, CConcr>>, XstsState<Prod2State<DAbstr, CAbstr>>> lazyState,
                    Prod2State<DConcr, CConcr> newConcrState) {
                final XstsState<Prod2State<DConcr, CConcr>> concrXstsState = lazyState.getConcrState();
                final XstsState<Prod2State<DConcr, CConcr>> newXstsState =
                    XstsState.of(newConcrState, concrXstsState.lastActionWasEnv(), concrXstsState.isInitialized());
                return lazyState.withConcrState(newXstsState);
            }
        };
    }

    public static <DConcr extends State, CConcr extends State, DAbstr extends State, CAbstr extends State> Lens<LazyState<XstsState<Prod2State<DConcr, CConcr>>, XstsState<Prod2State<DAbstr, CAbstr>>>, Prod2State<DAbstr, CAbstr>>
    createAbstrProd2Lens() {
        return new Lens<>() {
            @Override
            public Prod2State<DAbstr, CAbstr> get(LazyState<XstsState<Prod2State<DConcr, CConcr>>, XstsState<Prod2State<DAbstr, CAbstr>>> state) {
                return state.getAbstrState().getState();
            }
            @Override
            public LazyState<XstsState<Prod2State<DConcr, CConcr>>, XstsState<Prod2State<DAbstr, CAbstr>>> set(
                    LazyState<XstsState<Prod2State<DConcr, CConcr>>, XstsState<Prod2State<DAbstr, CAbstr>>> lazyState,
                    Prod2State<DAbstr, CAbstr> newAbstrState) {
                final XstsState<Prod2State<DAbstr, CAbstr>> abstrXstsState = lazyState.getAbstrState();
                final XstsState<Prod2State<DAbstr, CAbstr>> newXstsState =
                        XstsState.of(newAbstrState, abstrXstsState.lastActionWasEnv(), abstrXstsState.isInitialized());
                return lazyState.withAbstrState(newXstsState);
            }
        };
    }
}
