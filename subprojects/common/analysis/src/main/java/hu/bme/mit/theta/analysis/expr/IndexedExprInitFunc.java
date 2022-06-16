package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;

import java.util.Collection;
import java.util.Collections;

import static com.google.common.base.Preconditions.checkNotNull;

public final class IndexedExprInitFunc implements InitFunc<IndexedExprState, UnitPrec> {

    private final Expr<BoolType> initExpr;

    private IndexedExprInitFunc(final Expr<BoolType> initExpr) {
        this.initExpr = checkNotNull(initExpr);
    }

    public static IndexedExprInitFunc create(final Expr<BoolType> initExpr) {
        return new IndexedExprInitFunc(initExpr);
    }

    @Override
    public Collection<? extends IndexedExprState> getInitStates(UnitPrec prec) {
        final VarIndexing varIndexing = VarIndexingFactory.indexing(0);
        final Expr<BoolType> indexedInitExpr = PathUtils.unfold(initExpr, varIndexing);
        return Collections.singleton(IndexedExprState.of(indexedInitExpr, varIndexing));
    }
}
