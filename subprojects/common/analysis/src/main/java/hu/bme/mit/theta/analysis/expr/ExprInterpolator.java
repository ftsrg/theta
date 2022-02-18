package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Interpolator;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.*;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.Collection;
import java.util.Collections;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neq;
import static hu.bme.mit.theta.core.utils.PathUtils.unfold;

public final class ExprInterpolator implements Interpolator<BasicExprState, BasicExprState> {

    private final Solver solver;
    private final ItpSolver itpSolver;

    private ExprInterpolator(final Solver solver, final ItpSolver itpSolver) {
        this.solver = checkNotNull(solver);
        this.itpSolver = checkNotNull(itpSolver);
    }

    public static ExprInterpolator create(final Solver solver, final ItpSolver itpSolver) {
        return new ExprInterpolator(solver, itpSolver);
    }

    @Override
    public BasicExprState toItpDom(BasicExprState state) {
        return state;
    }

    @Override
    public BasicExprState interpolate(BasicExprState state1, BasicExprState state2) {
        try (WithPushPop wpp = new WithPushPop(solver)) {
            final ItpMarker A = itpSolver.createMarker();
            final ItpMarker B = itpSolver.createMarker();
            final ItpPattern pattern = itpSolver.createBinPattern(A, B);

            itpSolver.add(A, state1.toExpr());
            itpSolver.add(B, state2.toExpr());

            itpSolver.check();
            assert itpSolver.getStatus() == SolverStatus.UNSAT;

            final Interpolant itp = itpSolver.getInterpolant(pattern);
            final Expr<BoolType> itpExpr = itp.eval(A);

            return BasicExprState.of(itpExpr);
        }
    }

    @Override
    public boolean refutes(BasicExprState state1, BasicExprState state2) {
        try (WithPushPop wpp = new WithPushPop(solver)) {
            solver.add(unfold(state1.toExpr(), 0));
            solver.add(unfold(state2.toExpr(), 0));
            return solver.check().isUnsat();
        }
    }

    @Override
    public Collection<BasicExprState> complement(BasicExprState state) {
        final Expr<BoolType> notExpr = Not(state.toExpr());
        return Collections.singleton(BasicExprState.of(notExpr));
    }
}
