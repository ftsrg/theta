package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

public final class ExprLattice implements Lattice<BasicExprState> {

    private final PartialOrd<ExprState> partialOrd;

    private ExprLattice(final Solver solver) {
        partialOrd = ExprOrd.create(solver);
    }

    public static ExprLattice create(final Solver solver) {
        return new ExprLattice(solver);
    }

    @Override
    public BasicExprState top() {
        return BasicExprState.of(True());
    }

    @Override
    public BasicExprState bottom() {
        return BasicExprState.of(False());
    }

    @Override
    public BasicExprState meet(BasicExprState state1, BasicExprState state2) {
        final Expr<BoolType> andExpr = And(state1.toExpr(), state2.toExpr());
        return BasicExprState.of(andExpr);
    }

    @Override
    public BasicExprState join(BasicExprState state1, BasicExprState state2) {
        final Expr<BoolType> orExpr = Or(state1.toExpr(), state2.toExpr());
        return BasicExprState.of(orExpr);
    }

    @Override
    public boolean isLeq(BasicExprState state1, BasicExprState state2) {
        return partialOrd.isLeq(state1, state2);
    }
}
