package hu.bme.mit.theta.analysis.algorithm.lazy.expr;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprOrd;
import hu.bme.mit.theta.analysis.expr.IndexedExprState;
import hu.bme.mit.theta.analysis.expr.IndexedExprTransFunc;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.solver.Solver;

import static com.google.common.base.Preconditions.checkNotNull;

public final class ExprAnalysis implements Analysis<IndexedExprState, ExprAction, UnitPrec> {

    private final PartialOrd<IndexedExprState> partialOrd;
    private final ExprInitFunc initFunc;
    private final IndexedExprTransFunc transFunc;

    private ExprAnalysis(final Valuation initialValuation, final Solver solver) {
        checkNotNull(initialValuation);
        checkNotNull(solver);
        this.partialOrd = ExprOrd.create(solver)::isLeq;
        this.initFunc = ExprInitFunc.create(initialValuation);
        this.transFunc = IndexedExprTransFunc.getInstance();
    }

    public static ExprAnalysis create(final Valuation initialValuation, final Solver solver) {
        return new ExprAnalysis(initialValuation, solver);
    }

    @Override
    public PartialOrd<IndexedExprState> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public InitFunc<IndexedExprState, UnitPrec> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<IndexedExprState, ExprAction, UnitPrec> getTransFunc() {
        return transFunc;
    }
}
