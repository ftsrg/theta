package hu.bme.mit.theta.analysis.prod2.prod2explpred.dynamic;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.Prod2InitFunc;
import hu.bme.mit.theta.analysis.prod2.StrengtheningOperator;

public class DynamicInitFunc extends Prod2InitFunc<ExplState, PredState, ExplPrec, PredPrec> {

    protected DynamicInitFunc(InitFunc initFunc1, InitFunc initFunc2, StrengtheningOperator strengtheningOperator) {
        super(initFunc1, initFunc2, strengtheningOperator);
    }

    public static DynamicInitFunc createDynamic(
            final InitFunc<ExplState, ExplPrec> initFunc1, final InitFunc<PredState, PredPrec> initFunc2) {
        return createDynamic(initFunc1, initFunc2, (states, prec) -> states);
    }

    public static DynamicInitFunc createDynamic(
            final InitFunc<ExplState, ExplPrec> initFunc1, final InitFunc<PredState, PredPrec> initFunc2,
            final StrengtheningOperator<ExplState, PredState, ExplPrec, PredPrec> strengtheningOperator) {
        return new DynamicInitFunc(initFunc1, initFunc2, strengtheningOperator);
    }
}
