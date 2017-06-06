package hu.bme.mit.theta.core.type;

import hu.bme.mit.theta.core.expr.DivExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.MulExpr;

public interface Multiplicative<ExprType extends Multiplicative<ExprType>> extends Type {

	MulExpr<ExprType> Add(Iterable<? extends Expr<ExprType>> ops);

	DivExpr<ExprType> Div(Expr<ExprType> leftOp, Expr<ExprType> rightOp);

}
