package hu.bme.mit.theta.core.type;

import hu.bme.mit.theta.core.expr.EqExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.NeqExpr;

public interface Extensional<OpType extends Extensional<OpType>> extends Type {

	EqExpr<OpType> Eq(Expr<OpType> leftOp, Expr<OpType> rightOp);

	NeqExpr<OpType> Neq(Expr<OpType> leftOp, Expr<OpType> rightOp);

}
