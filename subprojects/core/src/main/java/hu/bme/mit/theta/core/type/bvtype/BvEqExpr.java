package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Arrays;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class BvEqExpr extends EqExpr<BvType> {

    private static final int HASH_SEED = 2487;
    private static final String OPERATOR_LABEL = "=";

    private BvEqExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        super(leftOp, rightOp);
    }

    public static BvEqExpr of(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return new BvEqExpr(leftOp, rightOp);
    }

    public static BvEqExpr create(final Expr<?> leftOp, final Expr<?> rightOp) {
        BvType bvType = (BvType) leftOp.getType();
        final Expr<BvType> newLeftOp = cast(leftOp, bvType);
        final Expr<BvType> newRightOp = cast(rightOp, bvType);
        return BvEqExpr.of(newLeftOp, newRightOp);
    }

    @Override
    public BoolType getType() {
        return Bool();
    }

    @Override
    public BoolLitExpr eval(final Valuation val) {
        final BvLitExpr leftOpVal = (BvLitExpr) getLeftOp().eval(val);
        final BvLitExpr rightOpVal = (BvLitExpr) getRightOp().eval(val);

        checkState(leftOpVal.isSigned() == rightOpVal.isSigned(), "Invalid operation");
        return Bool(Arrays.equals(leftOpVal.getValue(), rightOpVal.getValue()));
    }

    @Override
    public BvEqExpr with(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        if (leftOp == getLeftOp() && rightOp == getRightOp()) {
            return this;
        } else {
            return BvEqExpr.of(leftOp, rightOp);
        }
    }

    @Override
    public BvEqExpr withLeftOp(final Expr<BvType> leftOp) {
        return with(leftOp, getRightOp());
    }

    @Override
    public BvEqExpr withRightOp(final Expr<BvType> rightOp) {
        return with(getLeftOp(), rightOp);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof BvEqExpr) {
            final BvEqExpr that = (BvEqExpr) obj;
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
        return OPERATOR_LABEL;
    }
}
