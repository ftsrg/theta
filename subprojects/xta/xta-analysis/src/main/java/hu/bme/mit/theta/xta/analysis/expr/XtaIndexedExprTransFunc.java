package hu.bme.mit.theta.xta.analysis.expr;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.IndexedExprState;
import hu.bme.mit.theta.analysis.expr.IndexedExprTransFunc;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaDataAction;

import java.util.Collection;

public final class XtaIndexedExprTransFunc implements TransFunc<IndexedExprState, XtaAction, UnitPrec> {

    private final static XtaIndexedExprTransFunc INSTANCE = new XtaIndexedExprTransFunc();

    private final IndexedExprTransFunc transFunc;

    private XtaIndexedExprTransFunc() {
        transFunc = IndexedExprTransFunc.getInstance();
    }

    public static XtaIndexedExprTransFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends IndexedExprState> getSuccStates(IndexedExprState state, XtaAction action, UnitPrec prec) {
        final XtaDataAction dataAction = XtaDataAction.of(action);
        return transFunc.getSuccStates(state, dataAction, prec);
    }
}
