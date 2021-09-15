package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredAbstractors.Prod2ExplPredAbstractor;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;

import java.util.Collection;
import java.util.Collections;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

public class Prod2ExplPredDedicatedTransFunc<A extends ExprAction> implements TransFunc<Prod2State<ExplState, PredState>, A, Prod2Prec<ExplPrec, PredPrec>> {

    private final Prod2ExplPredAbstractor prod2ExplPredAbstractor;

    private Prod2ExplPredDedicatedTransFunc(final Prod2ExplPredAbstractor prod2ExplPredAbstractor){
        this.prod2ExplPredAbstractor = prod2ExplPredAbstractor;
    }

    public static <A extends ExprAction> Prod2ExplPredDedicatedTransFunc<A> create(final Prod2ExplPredAbstractor prod2ExplPredAbstractor){
        return new Prod2ExplPredDedicatedTransFunc<A>(prod2ExplPredAbstractor);
    }

    @Override
    public Collection<? extends Prod2State<ExplState, PredState>> getSuccStates(Prod2State<ExplState, PredState> state,
                                                                                A action, Prod2Prec<ExplPrec, PredPrec> prec) {
        checkNotNull(state);
        checkNotNull(action);
        checkNotNull(prec);

        final Collection<Prod2State<ExplState,PredState>> succStates = prod2ExplPredAbstractor.createStatesForExpr(
                And(state.toExpr(), action.toExpr()), VarIndexingFactory.indexing(0), prec, action.nextIndexing(), prec.getPrec1()::createState, 0);
        return succStates.isEmpty() ? Collections.singleton(Prod2State.of(ExplState.bottom(),PredState.bottom())) : succStates;
    }
}
