package hu.bme.mit.theta.xta.analysis.ClockPred;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.ZoneRefutation;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.zone.ClockPredPrec;
import hu.bme.mit.theta.analysis.zone.DBM;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.xta.analysis.prec.GlobalXtaPrec;
import hu.bme.mit.theta.xta.analysis.prec.XtaPrec;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneUtils;

import java.time.Clock;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public class XtaTraceChecker {


    private final ItpSolver solver;
    private final Expr<BoolType> init;

    private final Expr<BoolType> target;

    private final DBM initDBM;

    private final ZonePrec clocks;
    protected XtaTraceChecker(final Expr<BoolType> init, DBM initDBM, final Expr<BoolType> target, final ItpSolver solver,ZonePrec clocks ) {
        this.solver = solver;
        this.init = init;
        this.target = target;
        this.clocks = clocks;
        this.initDBM = initDBM;
    }

    public static XtaTraceChecker create(final Expr<BoolType> init, DBM initDBM, final Expr<BoolType> target, final ItpSolver solver, ZonePrec clocks) {
        return new XtaTraceChecker(init, initDBM, target, solver, clocks);
    }
    /*
    interpoláns az utolsó zonestate dbm-e és a a konkrét között amit itt számolok ki
     */
    public ExprTraceStatus<ZoneRefutation> check(Trace<ZoneState, XtaAction> trace)  {
        final int stateCount = trace.getStates().size();
        final int actionCount = trace.getActions().size();
        final List<ZoneState> concreteZoneStates = new ArrayList<ZoneState>(stateCount);
        final List<ZoneState> abstractPreZoneStates = new ArrayList<>(stateCount);

        abstractPreZoneStates.add( trace.getState(stateCount-1));
        concreteZoneStates.add(ZoneState.of(initDBM));
        for(int i = 1; i < stateCount; i++){
            concreteZoneStates.add(XtaZoneUtils.post(trace.getState(i-1), trace.getAction(i-1), clocks));
            abstractPreZoneStates.add(ZoneState.intersection(XtaZoneUtils.pre( abstractPreZoneStates.get(i-1), trace.getAction(actionCount-i), clocks),
                    trace.getState(stateCount-1-i)));
        }
        int maxindex = 0;
        boolean concretizable = true;
        Collections.reverse(abstractPreZoneStates);
        for (int i = stateCount-1; i >=0; i--){
            if(ZoneState.intersection(concreteZoneStates.get(i), abstractPreZoneStates.get(i)).isBottom()){
                maxindex = i;
                concretizable = false;
                break;
            }
        }
        if(concretizable){
            return ExprTraceStatus.feasible(null);
        }
        ZoneState interpolant = ZoneState.interpolant(concreteZoneStates.get(maxindex), abstractPreZoneStates.get(maxindex));
        return ExprTraceStatus.infeasible(ZoneRefutation.binary(maxindex, interpolant, clocks.getVars().stream().toList() ,stateCount));
    }



}
