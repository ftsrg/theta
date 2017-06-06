package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;

public interface Ordered<OpType extends Ordered<OpType>> extends Type {

	LtExpr<OpType> Lt(Expr<OpType> leftOp, Expr<OpType> rightOp);

	LeqExpr<OpType> Leq(Expr<OpType> leftOp, Expr<OpType> rightOp);

	GtExpr<OpType> Gt(Expr<OpType> leftOp, Expr<OpType> rightOp);

	GeqExpr<OpType> Geq(Expr<OpType> leftOp, Expr<OpType> rightOp);

}