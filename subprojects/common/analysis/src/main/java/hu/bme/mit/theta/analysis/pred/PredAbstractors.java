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
package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.common.collection.CollectionUtil;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.solver.AllSatSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/** Strategies for performing predicate abstraction over an expression. */
public class PredAbstractors {

    private PredAbstractors() {}

    /** Interface for performing predicate abstraction over an expression. */
    public interface PredAbstractor {

        /**
         * Create predicate states for a given expression with a given precision.
         *
         * @param expr Expression to be abstracted
         * @param exprIndexing Unfold indexing of the expression
         * @param prec Precision
         * @param precIndexing Unfold indexing of the precision
         * @return
         */
        Collection<PredState> createStatesForExpr(
                final Expr<BoolType> expr,
                final VarIndexing exprIndexing,
                final PredPrec prec,
                final VarIndexing precIndexing);

        default Collection<PredState> createStatesForExpr(
                final Expr<BoolType> expr,
                final VarIndexing exprIndexing,
                final PredPrec prec,
                final VarIndexing precIndexing,
                final PredState state,
                final ExprAction action) {
            return createStatesForExpr(expr, exprIndexing, prec, precIndexing);
        }
    }

    /**
     * Get the strategy that uses Boolean abstraction and splits the disjuncts.
     *
     * @param solver
     * @return
     */
    public static PredAbstractor booleanSplitAbstractor(final Solver solver) {
        return new BooleanAbstractor(solver, true);
    }

    /**
     * Get the strategy that uses Boolean abstraction (and keeps the formula as a whole).
     *
     * @param solver
     * @return
     */
    public static PredAbstractor booleanAbstractor(final Solver solver) {
        return new BooleanAbstractor(solver, false);
    }

    /**
     * Get the strategy that uses Cartesian abstraction.
     *
     * @param solver
     * @return
     */
    public static PredAbstractor cartesianAbstractor(final Solver solver) {
        return new CartesianAbstractor(solver);
    }

    /**
     * Replace the blocking-clause loop in boolean abstraction with the solver's own all-sat, where
     * it has one (see {@link hu.bme.mit.theta.solver.AllSatSolver}). Set from {@code --allsat}, or
     * from {@code -Dtheta.allsat} when no CLI drives it.
     *
     * <p>Off by default because the win is family-dependent. Measured against the loop it is 8-14%
     * faster on systemc and locks tasks, and <b>14x slower</b> on float-benchs/arctan_Pade, where
     * two of that run's nineteen abstractions cost MathSAT ~21 s each to enumerate while a plain
     * check-sat on the same assertions takes 14 ms. That cost is inside the solver, not here.
     */
    public static boolean allSatEnabled =
            Boolean.parseBoolean(System.getProperty("theta.allsat", "false"));

    private static final class BooleanAbstractor implements PredAbstractor {

        private final Solver solver;
        private final List<ConstDecl<BoolType>> actLits;
        private final String litPrefix;
        private static int instanceCounter = 0;
        private final boolean split;

        public BooleanAbstractor(final Solver solver, final boolean split) {
            this.solver = checkNotNull(solver);
            this.actLits = new ArrayList<>();
            this.litPrefix = "__" + getClass().getSimpleName() + "_" + instanceCounter + "_";
            instanceCounter++;
            this.split = split;
        }

        @Override
        public Collection<PredState> createStatesForExpr(
                final Expr<BoolType> expr,
                final VarIndexing exprIndexing,
                final PredPrec prec,
                final VarIndexing precIndexing) {
            checkNotNull(expr);
            checkNotNull(exprIndexing);
            checkNotNull(prec);
            checkNotNull(precIndexing);

            final List<Expr<BoolType>> preds = new ArrayList<>(prec.getPreds());
            generateActivationLiterals(preds.size());

            assert actLits.size() >= preds.size();

            final List<PredState> states = new LinkedList<>();
            try (WithPushPop wp = new WithPushPop(solver)) {
                solver.add(PathUtils.unfold(expr, exprIndexing));
                for (int i = 0; i < preds.size(); ++i) {
                    solver.add(
                            Iff(
                                    actLits.get(i).getRef(),
                                    PathUtils.unfold(preds.get(i), precIndexing)));
                }

                // Boolean predicate abstraction *is* all-sat over the activation literals. When
                // the solver can enumerate them itself we get the whole answer in one call; the
                // loop below emulates the same thing with one solver round trip per model, which
                // is all that portable SMT-LIB allows. Measured on systemc/pc_sfifo_1.cil-2:
                // 1832 abstractions cost 5587 check-sat calls through the loop.
                if (allSatEnabled
                        && solver instanceof AllSatSolver allSatSolver
                        && allSatSolver.supportsAllSat()) {
                    final var actLitsForPreds = actLits.subList(0, preds.size());
                    // check-allsat leaves the enumerated models blocked in the current scope,
                    // so give it its own push level rather than letting that leak into anything
                    // that reuses this solver afterwards.
                    try (WithPushPop allSatScope = new WithPushPop(solver)) {
                        // Distinct-by-construction in MathSAT (its all-sat does not repeat a
                        // cube unless -dpll.allsat_allow_duplicates is set), but the set is
                        // kept: PRED_BOOL folds these cubes into a single disjunction, so a
                        // repeated cube would silently enlarge every downstream expression.
                        final Set<PredState> distinct = new LinkedHashSet<>();
                        for (final Valuation model : allSatSolver.allSat(actLitsForPreds)) {
                            distinct.add(PredState.of(statePredsOf(model, preds, prec)));
                        }
                        states.addAll(distinct);
                    }
                    // -Dtheta.allsat.verify=true recomputes the same abstraction with the
                    // blocking-clause loop below and reports any disagreement. Diagnostic only,
                    // and expensive -- it makes all-sat strictly slower than not using it.
                    if (Boolean.getBoolean("theta.allsat.verify")) {
                        verifyAgainstLoop(states, preds, prec);
                    }
                    return collapse(states);
                }

                while (solver.check().isSat()) {
                    final Valuation model = solver.getModel();
                    final Set<Expr<BoolType>> newStatePreds = CollectionUtil.createSet();
                    final List<Expr<BoolType>> feedback = new LinkedList<>();
                    feedback.add(True());
                    for (int i = 0; i < preds.size(); ++i) {
                        final ConstDecl<BoolType> lit = actLits.get(i);
                        final Expr<BoolType> pred = preds.get(i);
                        final Optional<LitExpr<BoolType>> eval = model.eval(lit);
                        if (eval.isPresent()) {
                            if (eval.get().equals(True())) {
                                newStatePreds.add(pred);
                                feedback.add(lit.getRef());
                            } else {
                                newStatePreds.add(prec.negate(pred));
                                feedback.add(Not(lit.getRef()));
                            }
                        }
                    }
                    states.add(PredState.of(newStatePreds));
                    solver.add(Not(And(feedback)));
                }
            }
            return collapse(states);
        }

        /** Diagnostic: recompute with the blocking-clause loop and report disagreement. */
        private void verifyAgainstLoop(
                final List<PredState> allSatStates,
                final List<Expr<BoolType>> preds,
                final PredPrec prec) {
            final List<PredState> loopStates = new LinkedList<>();
            try (WithPushPop inner = new WithPushPop(solver)) {
                while (solver.check().isSat()) {
                    final Valuation model = solver.getModel();
                    final Set<Expr<BoolType>> sp = statePredsOf(model, preds, prec);
                    loopStates.add(PredState.of(sp));
                    final List<Expr<BoolType>> feedback = new LinkedList<>();
                    feedback.add(True());
                    int assigned = 0;
                    for (int i = 0; i < preds.size(); ++i) {
                        final Optional<LitExpr<BoolType>> e = model.eval(actLits.get(i));
                        if (e.isPresent()) {
                            assigned++;
                            feedback.add(
                                    e.get().equals(True())
                                            ? actLits.get(i).getRef()
                                            : Not(actLits.get(i).getRef()));
                        }
                    }
                    // If the model leaves a literal unassigned, the blocking clause below
                    // excludes every cube agreeing on the assigned literals -- not just the
                    // one found -- so the loop would skip cubes it never examined.
                    if (assigned < preds.size()) {
                        System.err.println(
                                "LOOP-PARTIAL-MODEL preds="
                                        + preds.size()
                                        + " assigned="
                                        + assigned
                                        + " (blocking clause over-blocks by 2^"
                                        + (preds.size() - assigned)
                                        + ")");
                    }
                    solver.add(Not(And(feedback)));
                }
            }
            final var a = CollectionUtil.createSet();
            a.addAll(allSatStates);
            final var b = CollectionUtil.createSet();
            b.addAll(loopStates);
            if (!a.equals(b)) {
                System.err.println(
                        "ALLSAT-MISMATCH preds="
                                + preds.size()
                                + " allsat="
                                + allSatStates.size()
                                + " loop="
                                + loopStates.size()
                                + "\n  allsat: "
                                + allSatStates
                                + "\n  loop  : "
                                + loopStates);
            }
        }

        /** Reads one model into the set of (possibly negated) predicates it satisfies. */
        private Set<Expr<BoolType>> statePredsOf(
                final Valuation model, final List<Expr<BoolType>> preds, final PredPrec prec) {
            final Set<Expr<BoolType>> newStatePreds = CollectionUtil.createSet();
            for (int i = 0; i < preds.size(); ++i) {
                final Optional<LitExpr<BoolType>> eval = model.eval(actLits.get(i));
                if (eval.isPresent()) {
                    newStatePreds.add(
                            eval.get().equals(True()) ? preds.get(i) : prec.negate(preds.get(i)));
                }
            }
            return newStatePreds;
        }

        /** PRED_BOOL folds the cubes into one disjunctive state; PRED_SPLIT keeps them apart. */
        private Collection<PredState> collapse(final List<PredState> states) {
            if (!split && states.size() > 1) {
                final Expr<BoolType> pred =
                        Or(states.stream().map(PredState::toExpr).collect(Collectors.toList()));
                return Collections.singleton(PredState.of(pred));
            } else {
                return states;
            }
        }

        private void generateActivationLiterals(final int n) {
            while (actLits.size() < n) {
                actLits.add(Decls.Const(litPrefix + actLits.size(), BoolExprs.Bool()));
            }
        }
    }

    private static final class CartesianAbstractor implements PredAbstractor {

        private final Solver solver;

        public CartesianAbstractor(final Solver solver) {
            this.solver = solver;
        }

        @Override
        public Collection<PredState> createStatesForExpr(
                final Expr<BoolType> expr,
                final VarIndexing exprIndexing,
                final PredPrec prec,
                final VarIndexing precIndexing) {
            final List<Expr<BoolType>> newStatePreds = new ArrayList<>();

            try (WithPushPop wp = new WithPushPop(solver)) {
                solver.add(PathUtils.unfold(expr, exprIndexing));
                solver.check();
                if (solver.getStatus().isUnsat()) {
                    return Collections.emptySet();
                }

                for (final Expr<BoolType> pred : prec.getPreds()) {
                    final boolean ponEntailed;
                    final boolean negEntailed;
                    try (WithPushPop wp1 = new WithPushPop(solver)) {
                        solver.add(PathUtils.unfold(prec.negate(pred), precIndexing));
                        ponEntailed = solver.check().isUnsat();
                    }
                    try (WithPushPop wp2 = new WithPushPop(solver)) {
                        solver.add(PathUtils.unfold(pred, precIndexing));
                        negEntailed = solver.check().isUnsat();
                    }

                    assert !(ponEntailed && negEntailed)
                            : "Ponated and negated predicates are both entailed.";

                    if (ponEntailed) {
                        newStatePreds.add(pred);
                    }
                    if (negEntailed) {
                        newStatePreds.add(prec.negate(pred));
                    }
                }
            }

            return Collections.singleton(PredState.of(newStatePreds));
        }

        @Override
        public Collection<PredState> createStatesForExpr(
                final Expr<BoolType> expr,
                final VarIndexing exprIndexing,
                final PredPrec prec,
                final VarIndexing precIndexing,
                final PredState state,
                final ExprAction action) {
            var actionExpr = action.toExpr();
            if (actionExpr.equals(True())) {
                var filteredPreds =
                        state.getPreds().stream()
                                .filter(
                                        p -> {
                                            var vars = ExprUtils.getVars(p);
                                            var indexing = action.nextIndexing();
                                            return vars.stream()
                                                    .allMatch(v -> indexing.get(v) == 0);
                                        })
                                .collect(Collectors.toList());
                return Collections.singleton(PredState.of(filteredPreds));
            }
            return createStatesForExpr(expr, exprIndexing, prec, precIndexing);
        }
    }
}
