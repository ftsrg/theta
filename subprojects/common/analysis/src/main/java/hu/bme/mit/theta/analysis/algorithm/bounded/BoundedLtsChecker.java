/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.bounded;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.EmptyProof;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprSimplifier;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.List;
import java.util.Objects;
import java.util.function.BiFunction;
import java.util.function.Predicate;

public class BoundedLtsChecker<S extends ExprState, A extends ExprAction, P extends Prec>
        implements SafetyChecker<EmptyProof, Trace<S, A>, P> {
    private final Solver solver;
    private final Analysis<S, A, ? super P> analysis;
    private final Predicate<? super S> target;
    private final LTS<? super S, A> lts;
    private final int bound;
    private final P defaultPrec;
    private final Deque<Transition<S, A>> transitions;
    private final ExprSimplifier simplifier = ExprSimplifier.create();
    private final BiFunction<A, List<A>, A> actionEnricher;

    public BoundedLtsChecker(
            LTS<? super S, A> lts,
            Analysis<S, A, ? super P> analysis,
            Predicate<? super S> target,
            int bound,
            Solver solver) {
        this(lts, analysis, target, bound, null, solver, (a, path) -> a);
    }

    public BoundedLtsChecker(
            LTS<? super S, A> lts,
            Analysis<S, A, ? super P> analysis,
            Predicate<? super S> target,
            int bound,
            P defaultPrec,
            Solver solver) {
        this(lts, analysis, target, bound, defaultPrec, solver, (a, path) -> a);
    }

    public BoundedLtsChecker(
            LTS<? super S, A> lts,
            Analysis<S, A, ? super P> analysis,
            Predicate<? super S> target,
            int bound,
            P defaultPrec,
            Solver solver,
            BiFunction<A, List<A>, A> actionEnricher) {
        this.solver = solver;
        this.analysis = analysis;
        this.target = target;
        this.lts = lts;
        this.bound = bound;
        this.defaultPrec = defaultPrec;
        this.actionEnricher = actionEnricher;
        transitions = new ArrayDeque<>(bound + 1);
    }

    private int depth() {
        return transitions.size();
    }

    @Override
    public SafetyResult<EmptyProof, Trace<S, A>> check(P prec) {
        return doCheck(prec == null ? defaultPrec : prec);
    }

    private SafetyResult<EmptyProof, Trace<S, A>> doCheck(P prec) {
        checkNotNull(prec, "No prec provided");
        var indexing = VarIndexingFactory.indexing(0);
        boolean safe = true;
        for (var initialState : analysis.getInitFunc().getInitStates(prec)) {
            if (initialState.isBottom()) {
                continue;
            }
            try (var wpp = new WithPushPop(solver)) {
                solver.add(PathUtils.unfold(initialState.toExpr(), indexing));
                if (!solver.check().isSat()) {
                    continue;
                }
                try {
                    transitions.addLast(new Transition<>(null, initialState, indexing));
                    var result = expand(prec);
                    if (result.isUnsafe()) {
                        return result;
                    }
                    if (!result.isSafe()) {
                        safe = false;
                    }
                } finally {
                    transitions.removeLast();
                }
            }
        }
        return getSafeResult(safe);
    }

    private SafetyResult<EmptyProof, Trace<S, A>> expand(P prec) {
        var transition = transitions.peekLast();
        assert transition != null : "No transition available";
        var state = transition.succState();
        if (target.test(state)) {
            return getCex();
        }
        if (bound > 0 && depth() > bound) {
            return SafetyResult.unknown();
        }
        var indexing = transition.succIndexing();
        var actions = lts.getEnabledActionsFor(state);
        // Collect the enriched actions from the current path (excluding the null initial action).
        // Each stored action's nextWriteTriples() already includes all accumulated writes up to
        // that point, so the last entry in this list carries the full accumulated write history.
        var pathActions =
                transitions.stream().map(Transition::action).filter(Objects::nonNull).toList();
        boolean safe = true;
        for (var action : actions) {
            var enrichedAction = actionEnricher.apply(action, pathActions);
            try (var wpp = new WithPushPop(solver)) {
                solver.add(PathUtils.unfold(enrichedAction.toExpr(), indexing));
                if (!solver.check().isSat()) {
                    continue;
                }
                var nextIndexing = enrichedAction.nextIndexing();
                for (var succState :
                        analysis.getTransFunc().getSuccStates(state, enrichedAction, prec)) {
                    if (succState.isBottom()) {
                        continue;
                    }
                    // Simplify the state expressions and do not call the SMT solver if it is
                    // trivially satisfied. This reduces the number of SMT solver calls with,
                    // e.g., UnitState, where the state expression is always trivial.
                    var succExpr =
                            simplifier.simplify(succState.toExpr(), ImmutableValuation.empty());
                    boolean needsCheck = !isTrue(succExpr);
                    if (needsCheck) {
                        solver.push();
                    }
                    try {
                        var succIndexing = indexing.add(nextIndexing);
                        if (needsCheck) {
                            solver.add(PathUtils.unfold(succExpr, succIndexing));
                            if (!solver.check().isSat()) {
                                continue;
                            }
                        }
                        try {
                            transitions.addLast(
                                    new Transition<>(enrichedAction, succState, succIndexing));
                            var result = expand(prec);
                            if (result.isUnsafe()) {
                                return result;
                            }
                            if (!result.isSafe()) {
                                safe = false;
                            }
                        } finally {
                            transitions.removeLast();
                        }
                    } finally {
                        if (needsCheck) {
                            solver.pop();
                        }
                    }
                }
            }
        }
        return getSafeResult(safe);
    }

    private boolean isTrue(Expr<BoolType> expr) {
        return expr instanceof BoolLitExpr boolLitExpr && boolLitExpr.getValue();
    }

    private SafetyResult<EmptyProof, Trace<S, A>> getCex() {
        var states = transitions.stream().map(Transition::succState).toList();
        var actions = transitions.stream().skip(1).map(Transition::action).toList();
        var trace = Trace.of(states, actions);
        return SafetyResult.unsafe(trace, EmptyProof.getInstance());
    }

    private SafetyResult<EmptyProof, Trace<S, A>> getSafeResult(boolean safe) {
        return safe ? SafetyResult.safe(EmptyProof.getInstance()) : SafetyResult.unknown();
    }

    private record Transition<S extends ExprState, A extends ExprAction>(
            A action, S succState, VarIndexing succIndexing) {}
}
