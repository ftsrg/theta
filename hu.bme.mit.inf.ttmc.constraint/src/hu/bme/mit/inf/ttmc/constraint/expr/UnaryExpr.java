package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface UnaryExpr<OpType extends Type, ExprType extends Type> extends Expr<ExprType> {
	public Expr<? extends OpType> getOp();
	public UnaryExpr<OpType, ExprType> withOp(final Expr<? extends OpType> op);

}
