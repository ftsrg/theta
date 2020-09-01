package hu.bme.mit.theta.core.type.inttype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.CastExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;

import static hu.bme.mit.theta.core.type.bvtype.BvExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public final class IntToBvExpr extends CastExpr<IntType, BvType> {
    private static final int HASH_SEED = 9664;
    private static final String OPERATOR_LABEL = "to_bv";

    private final int size;
    private final boolean isSigned;

    private IntToBvExpr(final Expr<IntType> op, int size, boolean isSigned) {
        super(op);
        this.size = size;
        this.isSigned = isSigned;
    }

    public static IntToBvExpr of(final Expr<IntType> op, int size, boolean isSigned) {
        return new IntToBvExpr(op, size, isSigned);
    }

    public static IntToBvExpr create(final Expr<?> op, int size, boolean isSigned) {
        final Expr<IntType> newOp = cast(op, Int());
        return IntToBvExpr.of(newOp, size, isSigned);
    }

    @Override
    public BvType getType() {
        return BvType(size, isSigned);
    }

    @Override
    public BvLitExpr eval(final Valuation val) {
        final IntLitExpr opVal = (IntLitExpr) getOp().eval(val);
        return opVal.toBv(size, isSigned);
    }

    @Override
    public IntToBvExpr with(final Expr<IntType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return IntToBvExpr.of(op, size, isSigned);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof IntToBvExpr) {
            final IntToBvExpr that = (IntToBvExpr) obj;
            return this.getOp().equals(that.getOp());
        } else {
            return false;
        }
    }

    @Override
    protected int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    public String getOperatorLabel() {
        return OPERATOR_LABEL;
    }
}
