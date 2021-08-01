package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.abstracttype.PosExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;

import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;
import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;

public final class FpPosExpr extends PosExpr<FpType> {

    private static final int HASH_SEED = 9424;
    private static final String OPERATOR_LABEL = "fppos";

    private FpPosExpr(final Expr<FpType> op) {
        super(op);
    }

    public static FpPosExpr of(final Expr<FpType> op) {
        return new FpPosExpr(op);
    }

    public static FpPosExpr create(final Expr<?> op) {
        final Expr<FpType> newOp = castFp(op);
        return FpPosExpr.of(newOp);
    }

    @Override
    public FpType getType() {
        return getOp().getType();
    }

    @Override
    public FpLitExpr eval(final Valuation val) {
        final FpLitExpr opVal = (FpLitExpr) getOp().eval(val);
        return opVal.pos();
    }

    @Override
    public FpPosExpr with(final Expr<FpType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return FpPosExpr.of(op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof FpPosExpr) {
            final FpPosExpr that = (FpPosExpr) obj;
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
