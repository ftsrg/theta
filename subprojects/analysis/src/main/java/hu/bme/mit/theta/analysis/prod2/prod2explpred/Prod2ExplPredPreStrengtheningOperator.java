package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.PreStrengtheningOperator;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.ArrayList;

import static com.google.common.base.Preconditions.checkNotNull;

public final class Prod2ExplPredPreStrengtheningOperator implements PreStrengtheningOperator<ExplState, PredState> {

    private Prod2ExplPredPreStrengtheningOperator(){}

    public static Prod2ExplPredPreStrengtheningOperator create(){
        return new Prod2ExplPredPreStrengtheningOperator();
    }

    @Override
    public ExplState strengthenState1(Prod2State<ExplState, PredState> state) {
        checkNotNull(state);

        return state.getState1();
    }

    @Override
    public PredState strengthenState2(Prod2State<ExplState, PredState> state) {
        checkNotNull(state);

        var explState = state.getState1();
        var predState = state.getState2();

        var exprs = new ArrayList<Expr<BoolType>>();

        exprs.addAll(predState.getPreds());
        exprs.add(explState.getVal().toExpr());

        return PredState.of(exprs);
    }
}
