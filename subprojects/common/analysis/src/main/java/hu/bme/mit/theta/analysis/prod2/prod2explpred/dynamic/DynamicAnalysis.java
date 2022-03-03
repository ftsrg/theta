package hu.bme.mit.theta.analysis.prod2.prod2explpred.dynamic;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.*;
import hu.bme.mit.theta.solver.Solver;

import static com.google.common.base.Preconditions.checkNotNull;

public class DynamicAnalysis<A extends StmtAction>
        implements Analysis<Prod2State<ExplState, PredState>,A, Prod2Prec<ExplPrec, PredPrec>> {

    private final PartialOrd<Prod2State<ExplState, PredState>> partialOrd;
    private final DynamicInitFunc initFunc;
    private final DynamicTransFunc transFunc;

    private DynamicAnalysis(final Solver solver, final Analysis<ExplState, ? super A, ExplPrec> analysis1, final Analysis<PredState, ? super A, PredPrec> analysis2,
                            final StrengtheningOperator<ExplState, PredState, ExplPrec, PredPrec> strengtheningOperator) {
        checkNotNull(analysis1);
        checkNotNull(analysis2);
        partialOrd = Prod2Ord.create(analysis1.getPartialOrd(), analysis2.getPartialOrd());
        initFunc = DynamicInitFunc.createDynamic(analysis1.getInitFunc(), analysis2.getInitFunc(), strengtheningOperator);
        transFunc = DynamicTransFunc.create(solver);
    }

    public static <A extends StmtAction> DynamicAnalysis<A> create(
            final Solver solver,
            final Analysis<ExplState, ? super A, ExplPrec> analysis1, final Analysis<PredState, ? super A, PredPrec> analysis2,
            final StrengtheningOperator<ExplState, PredState, ExplPrec, PredPrec> strengtheningOperator) {
        return new DynamicAnalysis<A>(solver, analysis1, analysis2, strengtheningOperator);
    }

    @Override
    public PartialOrd<Prod2State<ExplState, PredState>> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public InitFunc<Prod2State<ExplState, PredState>, Prod2Prec<ExplPrec, PredPrec>> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<Prod2State<ExplState, PredState>, A, Prod2Prec<ExplPrec, PredPrec>> getTransFunc() {
        return transFunc;
    }

}
