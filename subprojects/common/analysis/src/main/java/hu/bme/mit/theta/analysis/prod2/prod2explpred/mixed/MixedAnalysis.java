package hu.bme.mit.theta.analysis.prod2.prod2explpred.mixed;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.*;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredAbstractors;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredAnalysis;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredDedicatedTransFunc;
import hu.bme.mit.theta.solver.Solver;

import static com.google.common.base.Preconditions.checkNotNull;

public class MixedAnalysis<A extends StmtAction>
        implements Analysis<Prod2State<ExplState, PredState>, A, Prod2Prec<ExplPrec, PredPrec>> {

    private final PartialOrd<Prod2State<ExplState, PredState>> partialOrd;
    private final InitFunc<Prod2State<ExplState, PredState>, Prod2Prec<ExplPrec, PredPrec>> initFunc;
    private final MixedTransFunc transFunc;

    private MixedAnalysis(final Solver solver, final Analysis<ExplState, ? super A, ExplPrec> analysis1, final Analysis<PredState, ? super A, PredPrec> analysis2,
                          final StrengtheningOperator<ExplState, PredState, ExplPrec, PredPrec> strenghteningOperator) {
        checkNotNull(analysis1);
        checkNotNull(analysis2);
        partialOrd = Prod2Ord.create(analysis1.getPartialOrd(), analysis2.getPartialOrd());
        initFunc = Prod2InitFunc.create(analysis1.getInitFunc(), analysis2.getInitFunc(), strenghteningOperator);
        transFunc = MixedTransFunc.create(solver);
    }

    public static <A extends StmtAction> MixedAnalysis<A> create(
            final Solver solver,
            final Analysis<ExplState, ? super A, ExplPrec> analysis1, final Analysis<PredState, ? super A, PredPrec> analysis2,
            final StrengtheningOperator<ExplState, PredState, ExplPrec, PredPrec> strenghteningOperator) {
        return new MixedAnalysis<A>(solver, analysis1, analysis2, strenghteningOperator);
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
