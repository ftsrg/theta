package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;

import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public abstract class ModExpr<ExprType extends Divisible<ExprType>> extends BinaryExpr<ExprType, ExprType> {

    protected ModExpr(final Expr<ExprType> leftOp, final Expr<ExprType> rightOp) {
        super(leftOp, rightOp);
    }

    public static <ExprType extends Divisible<ExprType>> ModExpr<?> create2(final Expr<?> leftOp, final Expr<?> rightOp) {
        @SuppressWarnings("unchecked") final ExprType type = (ExprType) leftOp.getType();
        final Expr<ExprType> newLeftOp = cast(leftOp, type);
        final Expr<ExprType> newRightOp = cast(rightOp, type);
        return type.Mod(newLeftOp, newRightOp);
    }
}
