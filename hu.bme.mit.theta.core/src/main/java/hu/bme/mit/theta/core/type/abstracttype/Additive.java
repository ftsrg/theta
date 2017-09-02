package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

public interface Additive<ExprType extends Additive<ExprType>> extends Type {

	AddExpr<ExprType> Add(Iterable<? extends Expr<ExprType>> ops);

	SubExpr<ExprType> Sub(Expr<ExprType> leftOp, Expr<ExprType> rightOp);

	NegExpr<ExprType> Neg(Expr<ExprType> op);

}
