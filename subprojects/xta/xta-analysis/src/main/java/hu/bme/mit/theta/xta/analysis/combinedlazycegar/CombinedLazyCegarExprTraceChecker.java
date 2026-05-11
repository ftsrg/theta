/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xta.analysis.combinedlazycegar;

import static hu.bme.mit.theta.xta.analysis.combinedlazycegar.CombinedLazyCegarXtaUtils.forceCast;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;
import java.util.stream.Stream;

final class CombinedLazyCegarExprTraceChecker<R extends Refutation> implements ExprTraceChecker<R> {
    private final ExprTraceChecker<R> exprTraceChecker;
    private final Lens<
                    LazyState<
                            XtaState<Prod2State<? extends ExprState, ?>>,
                            XtaState<Prod2State<? extends ExprState, ?>>>,
                    Prod2State<? extends ExprState, ?>>
            concrProd2Lens;
    private final XtaSystem system;

    public CombinedLazyCegarExprTraceChecker(
            final ExprTraceChecker<R> exprTraceChecker,
            final Lens<
                            LazyState<
                                    XtaState<Prod2State<? extends ExprState, ?>>,
                                    XtaState<Prod2State<? extends ExprState, ?>>>,
                            Prod2State<? extends ExprState, ?>>
                    concrProd2Lens,
            final XtaSystem system) {
        this.exprTraceChecker = exprTraceChecker;
        this.concrProd2Lens = concrProd2Lens;
        this.system = system;
    }

    @Override
    public ExprTraceStatus<R> check(Trace<? extends ExprState, ? extends ExprAction> trace) {
        final Trace<
                        LazyState<
                                XtaState<Prod2State<? extends ExprState, ?>>,
                                XtaState<Prod2State<? extends ExprState, ?>>>,
                        XtaAction>
                typedTrace = forceCast(trace);

        final var newTrace =
                Trace.of(
                        Streams.concat(
                                        initialValuationToExprState(
                                                system.getInitVal(),
                                                concrProd2Lens
                                                        .get(typedTrace.getStates().get(0))
                                                        .getState1()
                                                        .toExpr()),
                                        typedTrace.getStates().stream()
                                                .skip(1)
                                                .map(s -> concrProd2Lens.get(s).getState1()))
                                .toList(),
                        typedTrace.getActions());

        return exprTraceChecker.check(newTrace);
    }

    private Stream<ExprState> initialValuationToExprState(
            final Valuation initialValuation, final Expr<BoolType> exprState) {
        return Stream.of(
                new ExprState() {
                    @Override
                    public Expr<BoolType> toExpr() {
                        return SmartBoolExprs.And(initialValuation.toExpr(), exprState);
                    }

                    @Override
                    public boolean isBottom() {
                        return false;
                    }
                });
    }
}
