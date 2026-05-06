package hu.bme.mit.theta.xta.analysis.expr;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprOrd;
import hu.bme.mit.theta.analysis.expr.IndexedExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XtaExprAnalysis implements Analysis<IndexedExprState, XtaAction, UnitPrec> {

    private final PartialOrd<IndexedExprState> partialOrd;
    private final XtaExprInitFunc initFunc;
    private final XtaIndexedExprTransFunc transFunc;

    private XtaExprAnalysis(final XtaSystem system, final Solver solver) {
        checkNotNull(system);
        checkNotNull(solver);
        partialOrd = ExprOrd.create(solver)::isLeq;
        initFunc = XtaExprInitFunc.create(system);
        transFunc = XtaIndexedExprTransFunc.getInstance();
    }

    public static XtaExprAnalysis create(final XtaSystem system, final Solver solver) {
        return new XtaExprAnalysis(system, solver);
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
    public TransFunc<IndexedExprState, XtaAction, UnitPrec> getTransFunc() {
        return transFunc;
    }
}
