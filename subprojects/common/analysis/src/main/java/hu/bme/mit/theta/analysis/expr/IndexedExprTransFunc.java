package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

import java.util.Collection;
import java.util.Collections;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

public final class IndexedExprTransFunc implements TransFunc<IndexedExprState, ExprAction, UnitPrec> {

    private final static IndexedExprTransFunc INSTANCE = new IndexedExprTransFunc();

    private IndexedExprTransFunc() {
    }

    public static IndexedExprTransFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends IndexedExprState> getSuccStates(IndexedExprState state, ExprAction action, UnitPrec prec) {
        final VarIndexing currentIndexing = state.getVarIndexing();
        final Expr<BoolType> succExpr = And(state.toExpr(), PathUtils.unfold(action.toExpr(), currentIndexing));
        final VarIndexing newIndexing = currentIndexing.add(action.nextIndexing());
        final IndexedExprState succState = IndexedExprState.of(succExpr, newIndexing);
        return Collections.singleton(succState);
    }
}
