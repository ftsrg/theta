package hu.bme.mit.theta.xta.analysis.ClockPred;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ZoneRefutation;
import hu.bme.mit.theta.analysis.zone.DBM;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.xta.analysis.XtaAction;

public class NoneTraceChecker extends XtaTraceChecker{
    private NoneTraceChecker(final Expr<BoolType> init, DBM initDBM, final Expr<BoolType> target, final ItpSolver solver,ZonePrec clocks ) {
        super(init, initDBM, target, solver, clocks);
    }

    public static NoneTraceChecker create(final Expr<BoolType> init, DBM initDBM, final Expr<BoolType> target, final ItpSolver solver, ZonePrec clocks) {
        return new NoneTraceChecker(init, initDBM, target, solver, clocks);
    }
    @Override
    public ExprTraceStatus<ZoneRefutation> check(Trace<ZoneState, XtaAction> trace)  {
        return ExprTraceStatus.feasible(null);
    }
}
