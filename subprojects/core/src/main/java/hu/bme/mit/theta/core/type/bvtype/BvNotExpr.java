package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.NegExpr;

import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;

public class BvNotExpr extends NegExpr<BvType> {

    private static final int HASH_SEED = 1527;
    private static final String OPERATOR_LABEL = "~";

    private BvNotExpr(final Expr<BvType> op) {
        super(op);
    }

    public static BvNotExpr of(final Expr<BvType> op) {
        return new BvNotExpr(op);
    }

    public static BvNotExpr create(final Expr<?> op) {
        final Expr<BvType> newOp = castBv(op);
        return BvNotExpr.of(newOp);
    }

    @Override
    public BvType getType() {
        return getOp().getType();
    }

    @Override
    public BvLitExpr eval(final Valuation val) {
        final BvLitExpr opVal = (BvLitExpr) getOp().eval(val);
        return opVal.not();
    }

    @Override
    public BvNotExpr with(final Expr<BvType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return BvNotExpr.of(op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof BvNotExpr) {
            final BvNotExpr that = (BvNotExpr) obj;
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
