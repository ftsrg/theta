package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.VarIndexing;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

public final class IndexedExprState implements ExprState {

    private final Expr<BoolType> indexedExpr;
    private final VarIndexing varIndexing;

    protected IndexedExprState(final Expr<BoolType> indexedExpr, final VarIndexing varIndexing) {
        this.indexedExpr = checkNotNull(indexedExpr);
        this.varIndexing = checkNotNull(varIndexing);
    }

    public static IndexedExprState of(final Expr<BoolType> indexedExpr, final VarIndexing varIndexing) {
        return new IndexedExprState(indexedExpr, varIndexing);
    }

    public static IndexedExprState bottom() {
        return new IndexedExprState(False(), VarIndexing.all(0));
    }

    public VarIndexing getVarIndexing() {
        return varIndexing;
    }

    @Override
    public Expr<BoolType> toExpr() {
        return indexedExpr;
    }

    @Override
    public boolean isBottom() {
        return indexedExpr.equals(False());
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(getClass().getSimpleName()).body()
                .add(indexedExpr)
                .add(varIndexing.toString())
                .toString();
    }
}
