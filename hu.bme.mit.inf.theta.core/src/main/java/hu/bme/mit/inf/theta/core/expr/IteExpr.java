package hu.bme.mit.inf.theta.core.expr;

import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;

public interface IteExpr<ExprType extends Type> extends Expr<ExprType> {
	public Expr<? extends BoolType> getCond();
	public Expr<? extends ExprType> getThen();
	public Expr<? extends ExprType> getElse();
	
	public IteExpr<ExprType> withOps(final Expr<? extends BoolType> cond, final Expr<? extends ExprType> then, final Expr<? extends ExprType> elze);
	
	public IteExpr<ExprType> withCond(final Expr<? extends BoolType> cond);
	
	public IteExpr<ExprType> withThen(final Expr<? extends ExprType> then);
	
	public IteExpr<ExprType> withElse(final Expr<? extends ExprType> elze);
}
