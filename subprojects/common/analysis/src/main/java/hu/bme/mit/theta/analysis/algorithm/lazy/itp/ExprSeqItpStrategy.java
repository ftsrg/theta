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
package hu.bme.mit.theta.analysis.algorithm.lazy.itp;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.function.Function;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

public final class ExprSeqItpStrategy<S extends State, A extends Action> extends ItpStrategy<ExprState, BasicExprState, S, A> {

    private final Function<A, StmtAction> actionTransform;
    private final ExprTraceChecker<ItpRefutation> traceChecker;
    private final Solver solver;

    public ExprSeqItpStrategy(final Lens<S, LazyState<ExprState, BasicExprState>> lens,
                              final Function<A, StmtAction> actionTransform,
                              final Lattice<BasicExprState> lattice,
                              final Concretizer<ExprState, BasicExprState> concretizer,
                              final Solver solver,
                              final ExprTraceChecker<ItpRefutation> traceChecker) {
        super(lens, lattice, concretizer);
        this.actionTransform = checkNotNull(actionTransform);
        this.traceChecker = checkNotNull(traceChecker);
        this.solver = checkNotNull(solver);
    }

    @Override
    public void cover(ArgNode<S, A> coveree, ArgNode<S, A> coverer, Collection<ArgNode<S, A>> uncoveredNodes) {
        final BasicExprState covererAbstrState = lens.get(coverer.getState()).getAbstrState();
        final Expr<BoolType> covererExpr = covererAbstrState.toExpr();
        final Expr<BoolType> complementExpr = Not(covererExpr);
        block(coveree, complementExpr, uncoveredNodes);
    }

    @Override
    public void disable(ArgNode<S, A> node, A action, S succState, Collection<ArgNode<S, A>> uncoveredNodes) {
        assert inconsistentState(lens.get(succState).getConcrState());
        final ExprAction exprAction = actionTransform.apply(action);
        final Expr<BoolType> badExpr = exprAction.toExpr();
        block(node, badExpr, uncoveredNodes);
    }

    private void block(final ArgNode<S, A> node, final Expr<BoolType> badExpr, final Collection<ArgNode<S, A>> uncoveredNodes) {
        try (WithPushPop wpp = new WithPushPop(solver)) {
            final BasicExprState abstrState = lens.get(node.getState()).getAbstrState();
            solver.add(PathUtils.unfold(abstrState.toExpr(), 0));
            solver.add(PathUtils.unfold(badExpr, 0));
            solver.check();
            if (solver.getStatus() == SolverStatus.UNSAT) {
                return;
            }
        }
        final Trace<ExprState, ExprAction> trace = traceToBlock(node, badExpr);
        final ExprTraceStatus<ItpRefutation> result = traceChecker.check(trace);
        assert result.isInfeasible();
        final ItpRefutation itpRefutation = result.asInfeasible().getRefutation();

        final int lastItpIdx = itpRefutation.size() - 1;
        assert itpRefutation.get(lastItpIdx).equals(False());

        ArgNode<S, A> traceNode = node;
        for (int i = lastItpIdx - 1; i >= 0; i--) {
            final Expr<BoolType> itp = itpRefutation.get(i);
            final BasicExprState itpState = BasicExprState.of(itp);

            strengthen(traceNode, itpState);
            maintainCoverage(traceNode, itpState, uncoveredNodes);

            if (i > 0) {
                assert traceNode.getParent().isPresent();
                traceNode = traceNode.getParent().get();
            } else {
                assert traceNode.getParent().isEmpty();
            }
        }
    }

    private Trace<ExprState, ExprAction> traceToBlock(ArgNode<S, A> node, Expr<BoolType> badExpr) {
        final List<ExprState> states = new ArrayList<>();
        final List<StmtAction> actions = new ArrayList<>();

        states.add(BasicExprState.of(badExpr));
        actions.add(skipStmtAction());

        ArgNode<S, A> traceNode = node;
        while (traceNode.getInEdge().isPresent()) {

            //states.add(BasicExprState.of(True()));
            states.add(lens.get(traceNode.getState()).getAbstrState());

            final ArgEdge<S, A> edge = traceNode.getInEdge().get();
            final A action = edge.getAction();
            final StmtAction exprAction = actionTransform.apply(action);
            actions.add(exprAction);

            traceNode = edge.getSource();
        }

        final ExprState initState = lens.get(traceNode.getState()).getConcrState();
        states.add(initState);

        return Trace.of(Lists.reverse(states), Lists.reverse(actions));
    }

    private static StmtAction skipStmtAction() {
        return new StmtAction() {
            @Override
            public List<Stmt> getStmts() {
                return Collections.singletonList(Stmts.Skip());
            }
        };
    }
}
