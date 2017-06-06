package hu.bme.mit.theta.core.type;

import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.NegExpr;
import hu.bme.mit.theta.core.expr.SubExpr;

public interface Additive<ExprType extends Additive<ExprType>> extends Type {

	AddExpr<ExprType> Add(Iterable<? extends Expr<ExprType>> ops);

	SubExpr<ExprType> Sub(Expr<ExprType> leftOp, Expr<ExprType> rightOp);

	NegExpr<ExprType> Neg(Expr<ExprType> op);

}
