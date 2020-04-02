package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.GtExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public class BvGtExpr extends GtExpr<BvType> {

    private static final int HASH_SEED = 6231;
    private static final String OPERATOR_LABEL = ">";

    private BvGtExpr(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        super(leftOp, rightOp);
        checkAllTypesEqual(leftOp, rightOp);
    }

    public static BvGtExpr of(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return new BvGtExpr(leftOp, rightOp);
    }

    public static BvGtExpr create(final Expr<?> leftOp, final Expr<?> rightOp) {
        final Expr<BvType> newLeftOp = castBv(leftOp);
        final Expr<BvType> newRightOp = castBv(rightOp);
        return BvGtExpr.of(newLeftOp, newRightOp);
    }

    @Override
    public BoolType getType() {
        return Bool();
    }

    @Override
    public LitExpr<BoolType> eval(final Valuation val) {
        final BvLitExpr leftOpVal = (BvLitExpr) getLeftOp().eval(val);
        final BvLitExpr rightOpVal = (BvLitExpr) getRightOp().eval(val);
        return leftOpVal.gt(rightOpVal);
    }

    @Override
    public BvGtExpr with(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        if (leftOp == getLeftOp() && rightOp == getRightOp()) {
            return this;
        } else {
            return BvGtExpr.of(leftOp, rightOp);
        }
    }

    @Override
    public BvGtExpr withLeftOp(final Expr<BvType> leftOp) {
        return with(leftOp, getRightOp());
    }

    @Override
    public BvGtExpr withRightOp(final Expr<BvType> rightOp) {
        return with(getLeftOp(), rightOp);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof BvGtExpr) {
            final BvGtExpr that = (BvGtExpr) obj;
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
