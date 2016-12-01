package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.Type;

public interface UnaryExpr<OpType extends Type, ExprType extends Type> extends Expr<ExprType> {
	Expr<? extends OpType> getOp();

	UnaryExpr<OpType, ExprType> withOp(final Expr<? extends OpType> op);

}
