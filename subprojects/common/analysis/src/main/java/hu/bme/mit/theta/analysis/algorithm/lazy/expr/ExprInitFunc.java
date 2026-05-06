package hu.bme.mit.theta.analysis.algorithm.lazy.expr;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.expr.IndexedExprInitFunc;
import hu.bme.mit.theta.analysis.expr.IndexedExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.model.Valuation;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public class ExprInitFunc implements InitFunc<IndexedExprState, UnitPrec> {

    private final IndexedExprInitFunc initFunc;

    private ExprInitFunc(final Valuation initialValuation) {
        checkNotNull(initialValuation);
        initFunc = IndexedExprInitFunc.create(initialValuation.toExpr());
    }

    public static ExprInitFunc create(final Valuation initialValuation) {
        return new ExprInitFunc(initialValuation);
    }

    @Override
    public Collection<? extends IndexedExprState> getInitStates(UnitPrec prec) {
        return initFunc.getInitStates(prec);
    }
}
