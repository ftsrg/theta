package hu.bme.mit.theta.xta.analysis.lazy;

import hu.bme.mit.theta.analysis.Lens;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.itp.ItpState;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.xta.analysis.XtaState;

public class LazyXtaLensUtils {

    public static <DConcr extends State, DAbstr extends ExprState> Lens<ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>>, ItpState<DConcr, DAbstr>>
    createItpDataLens() {
        final Lens<ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>>, DConcr> concrLens = createConcrDataLens();
        final Lens<ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>>, DAbstr> abstrLens = createAbstrDataLens();
        return new Lens<>() {
            @Override
            public ItpState<DConcr, DAbstr> get(ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> state) {
                final DConcr concrState = concrLens.get(state);
                final DAbstr abstrState = abstrLens.get(state);
                return ItpState.of(concrState, abstrState);
            }
            @Override
            public ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> set(
                    ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> itpState,
                    ItpState<DConcr, DAbstr> newItpDataState) {
                final XtaState<Prod2State<DConcr, ?>> newConcrState = concrLens.set(itpState, newItpDataState.getConcrState()).getConcrState();
                final XtaState<Prod2State<DAbstr, ?>> newAbstrState = abstrLens.set(itpState, newItpDataState.getAbstrState()).getAbstrState();
                return ItpState.of(newConcrState, newAbstrState);
            }
        };
    }

    public static <CConcr extends State, CAbstr extends ExprState> Lens<ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>>, ItpState<CConcr, CAbstr>>
    createItpClockLens() {
        final Lens<ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>>, CConcr> concrLens = createConcrClockLens();
        final Lens<ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>>, CAbstr> abstrLens = createAbstrClockLens();
        return new Lens<>() {
            @Override
            public ItpState<CConcr, CAbstr> get(ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> state) {
                final CConcr concrState = concrLens.get(state);
                final CAbstr abstrState = abstrLens.get(state);
                return ItpState.of(concrState, abstrState);
            }
            @Override
            public ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> set(
                    ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> itpState,
                    ItpState<CConcr, CAbstr> newItpDataState) {
                final XtaState<Prod2State<?, CConcr>> newConcrState = concrLens.set(itpState, newItpDataState.getConcrState()).getConcrState();
                final XtaState<Prod2State<?, CAbstr>> newAbstrState = abstrLens.set(itpState, newItpDataState.getAbstrState()).getAbstrState();
                return ItpState.of(newConcrState, newAbstrState);
            }
        };
    }

    public static <DConcr extends State, DAbstr extends State> Lens<ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>>, DConcr>
    createConcrDataLens() {
        return new Lens<>() {
            @Override
            public DConcr get(ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> state) {
                return state.getConcrState().getState().getState1();
            }
            @Override
            public ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> set(
                    ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> itpState,
                    DConcr newConcrDataState) {
                final XtaState<Prod2State<DConcr, ?>> concrXtaState = itpState.getConcrState();
                final Prod2State<DConcr, ?> concrState = concrXtaState.getState();
                final Prod2State<DConcr, ?> newConcrState = concrState.with1(newConcrDataState);
                final XtaState<Prod2State<DConcr, ?>> newConcrXtaState = concrXtaState.withState(newConcrState);
                return itpState.withConcrState(newConcrXtaState);
            }
        };
    }

    public static <DConcr extends State, DAbstr extends State> Lens<ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>>, DAbstr>
    createAbstrDataLens() {
        return new Lens<>() {
            @Override
            public DAbstr get(ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> state) {
                return state.getAbstrState().getState().getState1();
            }
            @Override
            public ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> set(
                    ItpState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> itpState,
                    DAbstr newAbstrDataState) {
                final XtaState<Prod2State<DAbstr, ?>> abstrXtaState = itpState.getAbstrState();
                final Prod2State<DAbstr, ?> abstrState = abstrXtaState.getState();
                final Prod2State<DAbstr, ?> newAbstrState = abstrState.with1(newAbstrDataState);
                final XtaState<Prod2State<DAbstr, ?>> newAbstrXtaState = abstrXtaState.withState(newAbstrState);
                return itpState.withAbstrState(newAbstrXtaState);
            }
        };
    }

    public static <CConcr extends State, CAbstr extends State> Lens<ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>>, CConcr>
    createConcrClockLens() {
        return new Lens<>() {
            @Override
            public CConcr get(ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> state) {
                return state.getConcrState().getState().getState2();
            }
            @Override
            public ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> set(
                    ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> itpState,
                    CConcr newConcrClockState) {
                final XtaState<Prod2State<?, CConcr>> concrXtaState = itpState.getConcrState();
                final Prod2State<?, CConcr> concrState = concrXtaState.getState();
                final Prod2State<?, CConcr> newConcrState = concrState.with2(newConcrClockState);
                final XtaState<Prod2State<?, CConcr>> newConcrXtaState = concrXtaState.withState(newConcrState);
                return itpState.withConcrState(newConcrXtaState);
            }
        };
    }

    public static <CConcr extends State, CAbstr extends State> Lens<ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>>, CAbstr>
    createAbstrClockLens() {
        return new Lens<>() {
            @Override
            public CAbstr get(ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> state) {
                return state.getAbstrState().getState().getState2();
            }
            @Override
            public ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> set(
                    ItpState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> itpState,
                    CAbstr newAbstrClockState) {
                final XtaState<Prod2State<?, CAbstr>> abstrXtaState = itpState.getAbstrState();
                final Prod2State<?, CAbstr> abstrState = abstrXtaState.getState();
                final Prod2State<?, CAbstr> newAbstrState = abstrState.with2(newAbstrClockState);
                final XtaState<Prod2State<?, CAbstr>> newAbstrXtaState = abstrXtaState.withState(newAbstrState);
                return itpState.withAbstrState(newAbstrXtaState);
            }
        };
    }

    public static <DConcr extends State, CConcr extends State, DAbstr extends State, CAbstr extends State> Lens<ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, Prod2State<DConcr, CConcr>>
    createConcrProd2Lens() {
        return new Lens<>() {
            @Override
            public Prod2State<DConcr, CConcr> get(ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>> state) {
                return state.getConcrState().getState();
            }
            @Override
            public ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>> set(
                    ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>> itpState,
                    Prod2State<DConcr, CConcr> newConcrState) {
                final XtaState<Prod2State<DConcr, CConcr>> concrXtaState = itpState.getConcrState();
                final XtaState<Prod2State<DConcr, CConcr>> newXtaState = concrXtaState.withState(newConcrState);
                return itpState.withConcrState(newXtaState);
            }
        };
    }
}
