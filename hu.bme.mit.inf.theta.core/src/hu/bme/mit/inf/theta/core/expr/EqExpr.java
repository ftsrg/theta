package hu.bme.mit.inf.theta.core.expr;

import hu.bme.mit.inf.theta.core.expr.EqExpr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;

public interface EqExpr extends BinaryExpr<Type, Type, BoolType> {
	
	@Override
	public EqExpr withOps(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp);
	
	@Override
	public EqExpr withLeftOp(final Expr<? extends Type> leftOp);

	@Override
	public EqExpr withRightOp(final Expr<? extends Type> rightOp);
	
}
