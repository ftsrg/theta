package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;

import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;

public final class FpNegExpr extends UnaryExpr<FpType, FpType> {

    private static final int HASH_SEED = 4622;
    private static final String OPERATOR_LABEL = "fpneg";

    private FpNegExpr(final Expr<FpType> op) {
        super(op);
    }

    public static FpNegExpr of(final Expr<FpType> op) {
        return new FpNegExpr(op);
    }

    public static FpNegExpr create(final Expr<?> op) {
        final Expr<FpType> newOp = castFp(op);
        return FpNegExpr.of(newOp);
    }

    @Override
    public FpType getType() {
        return getOp().getType();
    }

    @Override
    public FpLitExpr eval(final Valuation val) {
        final FpLitExpr opVal = (FpLitExpr) getOp().eval(val);
        return opVal.neg();
    }

    @Override
    public FpNegExpr with(final Expr<FpType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return FpNegExpr.of(op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof FpNegExpr) {
            final FpNegExpr that = (FpNegExpr) obj;
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
