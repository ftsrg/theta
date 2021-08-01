package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.SubExpr;

import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public final class FpSubExpr extends SubExpr<FpType> {
    private static final int HASH_SEED = 2498;
    private static final String OPERATOR = "fpsub";

    private final FpRoundingMode roundingMode;

    private FpSubExpr(final FpRoundingMode roundingMode, final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
        super(leftOp, rightOp);
        checkAllTypesEqual(leftOp, rightOp);
        this.roundingMode = roundingMode;
    }

    public static FpSubExpr of(final FpRoundingMode roundingMode, final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
        return new FpSubExpr(roundingMode, leftOp, rightOp);
    }

    public static FpSubExpr create(final FpRoundingMode roundingMode, final Expr<?> leftOp, final Expr<?> rightOp) {
        final Expr<FpType> newLeftOp = castFp(leftOp);
        final Expr<FpType> newRightOp = castFp(rightOp);
        return FpSubExpr.of(roundingMode, newLeftOp, newRightOp);
    }

    public FpRoundingMode getRoundingMode() {
        return roundingMode;
    }

    @Override
    public FpType getType() {
        return getOps().get(0).getType();
    }

    @Override
    public FpLitExpr eval(final Valuation val) {
        final FpLitExpr leftOpVal = (FpLitExpr) getLeftOp().eval(val);
        final FpLitExpr rightOpVal = (FpLitExpr) getRightOp().eval(val);

        return leftOpVal.sub(roundingMode, rightOpVal);
    }

    @Override
    public FpSubExpr with(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
        if (leftOp == getLeftOp() && rightOp == getRightOp()) {
            return this;
        } else {
            return FpSubExpr.of(roundingMode, leftOp, rightOp);
        }
    }

    @Override
    public FpSubExpr withLeftOp(final Expr<FpType> leftOp) {
        return with(leftOp, getRightOp());
    }

    @Override
    public FpSubExpr withRightOp(final Expr<FpType> rightOp) {
        return with(getLeftOp(), rightOp);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof FpSubExpr) {
            final FpSubExpr that = (FpSubExpr) obj;
            return this.getLeftOp().equals(that.getLeftOp()) && this.getRightOp().equals(that.getRightOp());
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
        return OPERATOR;
    }
}
