package hu.bme.mit.theta.core.type;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.GeqExpr;
import hu.bme.mit.theta.core.expr.GtExpr;
import hu.bme.mit.theta.core.expr.LeqExpr;
import hu.bme.mit.theta.core.expr.LtExpr;

public interface Ordered<OpType extends Ordered<OpType>> extends Type {

	LtExpr<OpType> Lt(Expr<OpType> leftOp, Expr<OpType> rightOp);

	LeqExpr<OpType> Leq(Expr<OpType> leftOp, Expr<OpType> rightOp);

	GtExpr<OpType> Gt(Expr<OpType> leftOp, Expr<OpType> rightOp);

	GeqExpr<OpType> Geq(Expr<OpType> leftOp, Expr<OpType> rightOp);

}