package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;

public interface Multiplicative<ExprType extends Multiplicative<ExprType>> extends Type {

	MulExpr<ExprType> Mul(Iterable<? extends Expr<ExprType>> ops);

	DivExpr<ExprType> Div(Expr<ExprType> leftOp, Expr<ExprType> rightOp);

}
