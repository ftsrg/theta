/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.StmtSimplifier;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

public class Prod2ExplPredStmtTransFunc<A extends StmtAction>
        implements TransFunc<Prod2State<ExplState, PredState>, A, Prod2Prec<ExplPrec, PredPrec>> {

    private final Solver solver;

    private Prod2ExplPredStmtTransFunc(final Solver solver) {
        this.solver = checkNotNull(solver);
    }

    public static <A extends StmtAction> Prod2ExplPredStmtTransFunc<A> create(final Solver solver) {
        return new Prod2ExplPredStmtTransFunc<A>(solver);
    }

    @Override
    public Collection<? extends Prod2State<ExplState, PredState>> getSuccStates(
            Prod2State<ExplState, PredState> state, A action, Prod2Prec<ExplPrec, PredPrec> prec) {
        checkNotNull(state);
        checkNotNull(action);
        checkNotNull(prec);

        final var sequence = SequenceStmt.of(action.getStmts());
        final var simplifyResult =
                StmtSimplifier.simplifyStmtAndReturnValuation(state.getState1(), sequence);
        final var stmtUnfoldResult =
                StmtUtils.toExpr(simplifyResult.getSecond(), VarIndexingFactory.indexing(0));
        final var nextIndex = stmtUnfoldResult.getIndexing();

        final Expr<BoolType> expr = And(state.toExpr(), And(stmtUnfoldResult.getExprs()));

        try (WithPushPop wp = new WithPushPop(solver)) {
            final List<Expr<BoolType>> newStatePreds = new ArrayList<>();

            solver.add(PathUtils.unfold(expr, VarIndexingFactory.indexing(0)));
            solver.check();
            if (solver.getStatus().isUnsat()) {
                return Collections.emptySet();
            }

            final var predPrec = prec.getPrec2();

            for (final Expr<BoolType> pred : predPrec.getPreds()) {
                final boolean ponEntailed;
                final boolean negEntailed;
                try (WithPushPop wp1 = new WithPushPop(solver)) {
                    solver.add(PathUtils.unfold(predPrec.negate(pred), nextIndex));
                    ponEntailed = solver.check().isUnsat();
                }
                try (WithPushPop wp2 = new WithPushPop(solver)) {
                    solver.add(PathUtils.unfold(pred, nextIndex));
                    negEntailed = solver.check().isUnsat();
                }

                assert !(ponEntailed && negEntailed)
                        : "Ponated and negated predicates are both entailed.";

                if (ponEntailed) {
                    newStatePreds.add(pred);
                }
                if (negEntailed) {
                    newStatePreds.add(predPrec.negate(pred));
                }
            }

            final ExplPrec explPrec = prec.getPrec1();
            final MutableValuation noSolverValuation = new MutableValuation();
            final List<VarDecl<?>> uncertainVars = new ArrayList<>();
            for (var v : explPrec.getVars()) {
                final var simplifyRes = simplifyResult.getFirst().eval(v);
                if (simplifyRes.isPresent()) {
                    noSolverValuation.put(v, simplifyRes.get());
                } else {
                    uncertainVars.add(v);
                }
            }

            final ExplState newExplState;
            if (uncertainVars.isEmpty()) {
                newExplState = ExplState.of(noSolverValuation);
            } else {
                newStatePreds.forEach(it -> solver.add(PathUtils.unfold(it, nextIndex)));

                // Maxenum = 1 check
                solver.check();
                assert solver.getStatus().isSat();
                final Valuation model = solver.getModel();
                final Valuation valuation = PathUtils.extractValuation(model, nextIndex);
                final ExplState newState = ExplPrec.of(uncertainVars).createState(valuation);
                solver.add(Not(PathUtils.unfold(newState.toExpr(), nextIndex)));
                solver.check();
                if (solver.getStatus().isUnsat()) {
                    newExplState = ExplState.of(noSolverValuation.putAll(newState));
                } else {
                    newExplState = ExplState.of(noSolverValuation);
                }
            }

            return Collections.singleton(Prod2State.of(newExplState, PredState.of(newStatePreds)));
        }
    }
}
