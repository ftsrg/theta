package hu.bme.mit.theta.core.type.clocktype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;

import static com.google.common.base.Preconditions.checkArgument;

public final class ClockDiffExpr extends BinaryExpr<ClockType, ClockType> {

    private static final int HASH_SEED = 471867;
    private static final String OPERATOR_LABEL = "-";

    protected ClockDiffExpr(Expr<ClockType> leftOp, Expr<ClockType> rightOp) {
        super(leftOp, rightOp);
    }

    public static ClockDiffExpr of(Expr<ClockType> leftOp, Expr<ClockType> rightOp) {
        checkArgument(leftOp instanceof RefExpr);
        checkArgument(rightOp instanceof RefExpr);
        return new ClockDiffExpr(leftOp, rightOp);
    }

    @Override
    public BinaryExpr<ClockType, ClockType> with(Expr<ClockType> leftOp, Expr<ClockType> rightOp) {
        if (leftOp == getLeftOp() && rightOp == getRightOp()) {
            return this;
        } else {
            return ClockDiffExpr.of(leftOp, rightOp);
        }
    }

    @Override
    public BinaryExpr<ClockType, ClockType> withLeftOp(Expr<ClockType> leftOp) {
        return with(leftOp, getRightOp());
    }

    @Override
    public BinaryExpr<ClockType, ClockType> withRightOp(Expr<ClockType> rightOp) {
        return with(getLeftOp(), rightOp);
    }

    @Override
    protected int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    public String getOperatorLabel() {
        return OPERATOR_LABEL;
    }

    @Override
    public ClockType getType() {
        return ClockType.getInstance();
    }

    @Override
    public LitExpr<ClockType> eval(Valuation val) {
        throw new UnsupportedOperationException();
    }
}
