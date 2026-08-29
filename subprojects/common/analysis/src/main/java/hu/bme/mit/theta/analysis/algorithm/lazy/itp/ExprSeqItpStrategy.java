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

package hu.bme.mit.theta.analysis.algorithm.lazy.itp;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStatistics;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public final class ExprSeqItpStrategy<S extends State, A extends Action>
        extends ItpStrategy<ExprState, BasicExprState, S, A> {

    private final Lens<A, ExprAction> actionLens;
    private final ExprTraceChecker<ItpRefutation> traceChecker;
    private final Solver solver;

    public ExprSeqItpStrategy(
            final Lens<S, LazyState<ExprState, BasicExprState>> lens,
            final Lens<A, ExprAction> actionLens,
            final Lattice<BasicExprState> lattice,
            final Concretizer<ExprState, BasicExprState> concretizer,
            final Solver solver,
            final ExprTraceChecker<ItpRefutation> traceChecker) {
        super(lens, lattice, concretizer);
        this.actionLens = checkNotNull(actionLens);
        this.traceChecker = checkNotNull(traceChecker);
        this.solver = checkNotNull(solver);
    }

    @Override
    public void cover(
            final ArgNode<S, A> coveree,
            final ArgNode<S, A> coverer,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {
        stats.startCloseRefinement();
        block(coveree, Not(abstrState(coverer).toExpr()), uncoveredNodes, stats);
        stats.stopCloseRefinement();
    }

    @Override
    public void disable(
            final ArgNode<S, A> node,
            final A action,
            final S succState,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {
        assert inconsistentState(lens.get(succState).getConcrState());
        stats.startExpandRefinement();
        block(node, actionLens.get(action).toExpr(), uncoveredNodes, stats);
        stats.stopExpandRefinement();
    }

    private void block(
            final ArgNode<S, A> node,
            final Expr<BoolType> badExpr,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {
        if (isAlreadyExcluded(node, badExpr)) {
            return;
        }
        stats.refine();

        final Trace<ExprState, ExprAction> badTrace = getAbstrTraceTo(node, badExpr);

        final ExprTraceStatus<ItpRefutation> status = traceChecker.check(badTrace);
        assert status.isInfeasible();
        final ItpRefutation refutation = status.asInfeasible().getRefutation();

        final List<Expr<BoolType>> itpExprs = new ArrayList<>(refutation.toList());
        assert itpExprs.getLast().equals(False());
        itpExprs.removeLast();

        ArgNode<S, A> currentNode = node;
        boolean visitedRoot = false;
        for (final Expr<BoolType> itpExpr : itpExprs.reversed()) {
            assert !visitedRoot;

            final BasicExprState interpolant = BasicExprState.of(itpExpr);
            strengthen(currentNode, interpolant);
            maintainCoverage(currentNode, interpolant, uncoveredNodes);

            if (currentNode.getParent().isPresent()) {
                currentNode = currentNode.getParent().get();
            } else {
                visitedRoot = true;
            }
        }
        assert visitedRoot;
    }

    private boolean isAlreadyExcluded(final ArgNode<S, A> node, final Expr<BoolType> expr) {
        try (WithPushPop wpp = new WithPushPop(solver)) {
            final BasicExprState abstrState = abstrState(node);
            solver.add(PathUtils.unfold(abstrState.toExpr(), 0));
            solver.add(PathUtils.unfold(expr, 0));
            solver.check();
            return (solver.getStatus() == SolverStatus.UNSAT);
        }
    }

    private Trace<ExprState, ExprAction> getAbstrTraceTo(
            final ArgNode<S, A> node, final Expr<BoolType> expr) {
        final List<ExprState> states = new ArrayList<>();
        final List<ExprAction> actions = new ArrayList<>();

        states.add(BasicExprState.of(expr));
        actions.add(TrueExprAction.getInstance());

        ArgNode<S, A> currentNode = node;
        while (currentNode.getInEdge().isPresent()) {

            states.add(abstrState(currentNode));

            final ArgEdge<S, A> edge = currentNode.getInEdge().get();
            actions.add(actionLens.get(edge.getAction()));

            currentNode = edge.getSource();
        }

        final ArgNode<S, A> initNode = currentNode;
        states.add(concrState(initNode));

        return Trace.of(Lists.reverse(states), Lists.reverse(actions));
    }

    private ExprState concrState(final ArgNode<S, A> node) {
        return lens.get(node.getState()).getConcrState();
    }

    private BasicExprState abstrState(final ArgNode<S, A> node) {
        return lens.get(node.getState()).getAbstrState();
    }

    private static final class TrueExprAction implements ExprAction {

        private static final TrueExprAction INSTANCE = new TrueExprAction();

        public static TrueExprAction getInstance() {
            return INSTANCE;
        }

        @Override
        public Expr<BoolType> toExpr() {
            return True();
        }

        @Override
        public VarIndexing nextIndexing() {
            return VarIndexingFactory.indexing(0);
        }
    }
}
