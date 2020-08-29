package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

public interface Divisible<ExprType extends Divisible<ExprType>> extends Type {

    ModExpr<ExprType> Mod(Expr<ExprType> leftOp, Expr<ExprType> rightOp);

    RemExpr<ExprType> Rem(Expr<ExprType> leftOp, Expr<ExprType> rightOp);
}
