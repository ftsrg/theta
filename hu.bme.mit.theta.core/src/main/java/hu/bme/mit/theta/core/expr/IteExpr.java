package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;

public interface IteExpr<ExprType extends Type> extends Expr<ExprType> {
	Expr<? extends BoolType> getCond();

	Expr<? extends ExprType> getThen();

	Expr<? extends ExprType> getElse();

	IteExpr<ExprType> withOps(final Expr<? extends BoolType> cond, final Expr<? extends ExprType> then,
			final Expr<? extends ExprType> elze);

	IteExpr<ExprType> withCond(final Expr<? extends BoolType> cond);

	IteExpr<ExprType> withThen(final Expr<? extends ExprType> then);

	IteExpr<ExprType> withElse(final Expr<? extends ExprType> elze);
}
