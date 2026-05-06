package hu.bme.mit.theta.xta.analysis.expr;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.expr.IndexedExprInitFunc;
import hu.bme.mit.theta.analysis.expr.IndexedExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.xta.XtaSystem;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XtaExprInitFunc implements InitFunc<IndexedExprState, UnitPrec> {

    private final IndexedExprInitFunc initFunc;

    private XtaExprInitFunc(final XtaSystem system) {
        checkNotNull(system);
        initFunc = IndexedExprInitFunc.create(system.getInitVal().toExpr());
    }

    public static XtaExprInitFunc create(final XtaSystem system) {
        return new XtaExprInitFunc(system);
    }

    @Override
    public Collection<? extends IndexedExprState> getInitStates(UnitPrec prec) {
        return initFunc.getInitStates(prec);
    }
}
