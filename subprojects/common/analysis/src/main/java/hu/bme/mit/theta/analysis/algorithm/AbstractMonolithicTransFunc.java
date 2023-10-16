package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

public abstract class AbstractMonolithicTransFunc implements MonolithicTransFunc {
    protected Expr<BoolType> transExpr;
    protected Expr<BoolType> initExpr;
    protected VarIndexing firstIndex;
    protected VarIndexing offsetIndex;
    protected Expr<BoolType> propExpr;

    @Override
    public Expr<BoolType> getTransExpr() {
        return transExpr;
    }

    @Override
    public Expr<BoolType> getInitExpr() {
        return initExpr;
    }

    @Override
    public Expr<BoolType> getPropExpr() {
        return propExpr;
    }

    @Override
    public VarIndexing getInitIndexing() {
        return firstIndex;
    }

    @Override
    public VarIndexing getOffsetIndexing() {
        return offsetIndex;
    }
}
