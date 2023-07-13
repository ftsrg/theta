/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xta.analysis.lazy;

import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.xta.analysis.XtaState;

public final class LazyXtaLensUtils {

    public static <DConcr extends State, DAbstr extends ExprState> Lens<LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>>, LazyState<DConcr, DAbstr>>
    createLazyDataLens() {
        final Lens<LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>>, DConcr> concrLens = createConcrDataLens();
        final Lens<LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>>, DAbstr> abstrLens = createAbstrDataLens();
        return new Lens<>() {
            @Override
            public LazyState<DConcr, DAbstr> get(LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> state) {
                final DConcr concrState = concrLens.get(state);
                if (concrState.isBottom()) {
                    return LazyState.bottom(concrState);
                } else {
                    final DAbstr abstrState = abstrLens.get(state);
                    return LazyState.of(concrState, abstrState);
                }
            }

            @Override
            public LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> set(
                    LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> lazyState,
                    LazyState<DConcr, DAbstr> newItpDataState) {
                final XtaState<Prod2State<DConcr, ?>> newConcrState = concrLens.set(lazyState, newItpDataState.getConcrState()).getConcrState();
                final XtaState<Prod2State<DAbstr, ?>> newAbstrState = abstrLens.set(lazyState, newItpDataState.getAbstrState()).getAbstrState();
                return LazyState.of(newConcrState, newAbstrState);
            }
        };
    }

    public static <CConcr extends State, CAbstr extends ExprState> Lens<LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>>, LazyState<CConcr, CAbstr>>
    createLazyClockLens() {
        final Lens<LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>>, CConcr> concrLens = createConcrClockLens();
        final Lens<LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>>, CAbstr> abstrLens = createAbstrClockLens();
        return new Lens<>() {
            @Override
            public LazyState<CConcr, CAbstr> get(LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> state) {
                final CConcr concrState = concrLens.get(state);
                if (concrState.isBottom()) {
                    return LazyState.bottom(concrState);
                } else {
                    final CAbstr abstrState = abstrLens.get(state);
                    return LazyState.of(concrState, abstrState);
                }
            }

            @Override
            public LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> set(
                    LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> lazyState,
                    LazyState<CConcr, CAbstr> newItpDataState) {
                final XtaState<Prod2State<?, CConcr>> newConcrState = concrLens.set(lazyState, newItpDataState.getConcrState()).getConcrState();
                final XtaState<Prod2State<?, CAbstr>> newAbstrState = abstrLens.set(lazyState, newItpDataState.getAbstrState()).getAbstrState();
                return LazyState.of(newConcrState, newAbstrState);
            }
        };
    }

    public static <DConcr extends State, DAbstr extends State> Lens<LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>>, DConcr>
    createConcrDataLens() {
        return new Lens<>() {
            @Override
            public DConcr get(LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> state) {
                return state.getConcrState().getState().getState1();
            }

            @Override
            public LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> set(
                    LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> lazyState,
                    DConcr newConcrDataState) {
                final XtaState<Prod2State<DConcr, ?>> concrXtaState = lazyState.getConcrState();
                final Prod2State<DConcr, ?> concrState = concrXtaState.getState();
                final Prod2State<DConcr, ?> newConcrState = concrState.with1(newConcrDataState);
                final XtaState<Prod2State<DConcr, ?>> newConcrXtaState = concrXtaState.withState(newConcrState);
                return lazyState.withConcrState(newConcrXtaState);
            }
        };
    }

    public static <DConcr extends State, DAbstr extends State> Lens<LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>>, DAbstr>
    createAbstrDataLens() {
        return new Lens<>() {
            @Override
            public DAbstr get(LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> state) {
                return state.getAbstrState().getState().getState1();
            }

            @Override
            public LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> set(
                    LazyState<XtaState<Prod2State<DConcr, ?>>, XtaState<Prod2State<DAbstr, ?>>> lazyState,
                    DAbstr newAbstrDataState) {
                final XtaState<Prod2State<DAbstr, ?>> abstrXtaState = lazyState.getAbstrState();
                final Prod2State<DAbstr, ?> abstrState = abstrXtaState.getState();
                final Prod2State<DAbstr, ?> newAbstrState = abstrState.with1(newAbstrDataState);
                final XtaState<Prod2State<DAbstr, ?>> newAbstrXtaState = abstrXtaState.withState(newAbstrState);
                return lazyState.withAbstrState(newAbstrXtaState);
            }
        };
    }

    public static <CConcr extends State, CAbstr extends State> Lens<LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>>, CConcr>
    createConcrClockLens() {
        return new Lens<>() {
            @Override
            public CConcr get(LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> state) {
                return state.getConcrState().getState().getState2();
            }

            @Override
            public LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> set(
                    LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> lazyState,
                    CConcr newConcrClockState) {
                final XtaState<Prod2State<?, CConcr>> concrXtaState = lazyState.getConcrState();
                final Prod2State<?, CConcr> concrState = concrXtaState.getState();
                final Prod2State<?, CConcr> newConcrState = concrState.with2(newConcrClockState);
                final XtaState<Prod2State<?, CConcr>> newConcrXtaState = concrXtaState.withState(newConcrState);
                return lazyState.withConcrState(newConcrXtaState);
            }
        };
    }

    public static <CConcr extends State, CAbstr extends State> Lens<LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>>, CAbstr>
    createAbstrClockLens() {
        return new Lens<>() {
            @Override
            public CAbstr get(LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> state) {
                return state.getAbstrState().getState().getState2();
            }

            @Override
            public LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> set(
                    LazyState<XtaState<Prod2State<?, CConcr>>, XtaState<Prod2State<?, CAbstr>>> lazyState,
                    CAbstr newAbstrClockState) {
                final XtaState<Prod2State<?, CAbstr>> abstrXtaState = lazyState.getAbstrState();
                final Prod2State<?, CAbstr> abstrState = abstrXtaState.getState();
                final Prod2State<?, CAbstr> newAbstrState = abstrState.with2(newAbstrClockState);
                final XtaState<Prod2State<?, CAbstr>> newAbstrXtaState = abstrXtaState.withState(newAbstrState);
                return lazyState.withAbstrState(newAbstrXtaState);
            }
        };
    }

    public static <DConcr extends State, CConcr extends State, DAbstr extends State, CAbstr extends State> Lens<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, Prod2State<DConcr, CConcr>>
    createConcrProd2Lens() {
        return new Lens<>() {
            @Override
            public Prod2State<DConcr, CConcr> get(LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>> state) {
                return state.getConcrState().getState();
            }

            @Override
            public LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>> set(
                    LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>> lazyState,
                    Prod2State<DConcr, CConcr> newConcrState) {
                final XtaState<Prod2State<DConcr, CConcr>> concrXtaState = lazyState.getConcrState();
                final XtaState<Prod2State<DConcr, CConcr>> newXtaState = concrXtaState.withState(newConcrState);
                return lazyState.withConcrState(newXtaState);
            }
        };
    }
}
