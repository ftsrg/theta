package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;

import java.util.Collection;
import java.util.Collections;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

public final class IndexedExprInvTransFunc implements InvTransFunc<IndexedExprState, ExprAction, UnitPrec> {

    private final static IndexedExprInvTransFunc INSTANCE = new IndexedExprInvTransFunc();

    private IndexedExprInvTransFunc() {
    }

    public static IndexedExprInvTransFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends IndexedExprState> getPreStates(IndexedExprState state, ExprAction action, UnitPrec prec) {
        final VarIndexing currentIndexing = state.getVarIndexing();
        final Expr<BoolType> preExpr = And(state.toExpr(), PathUtils.unfoldReverse(action.toExpr(), currentIndexing));
        final VarIndexing newIndexing = currentIndexing.add(action.nextIndexing());
        final IndexedExprState preState = IndexedExprState.of(preExpr, newIndexing);
        return Collections.singleton(preState);
    }
}
