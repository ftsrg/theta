package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;

import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public abstract class RemExpr<ExprType extends Divisible<ExprType>> extends BinaryExpr<ExprType, ExprType> {

    protected RemExpr(final Expr<ExprType> leftOp, final Expr<ExprType> rightOp) {
        super(leftOp, rightOp);
    }

    public static <ExprType extends Divisible<ExprType>> RemExpr<?> create2(final Expr<?> leftOp, final Expr<?> rightOp) {
        @SuppressWarnings("unchecked") final ExprType type = (ExprType) leftOp.getType();
        final Expr<ExprType> newLeftOp = cast(leftOp, type);
        final Expr<ExprType> newRightOp = cast(rightOp, type);
        return type.Rem(newLeftOp, newRightOp);
    }
}
