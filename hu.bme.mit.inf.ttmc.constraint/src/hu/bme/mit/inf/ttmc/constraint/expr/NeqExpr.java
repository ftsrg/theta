package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface NeqExpr extends BinaryExpr<Type, Type, BoolType> {
	
	@Override
	public NeqExpr withOps(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp);

	@Override
	public NeqExpr withLeftOp(final Expr<? extends Type> leftOp);

	@Override
	public NeqExpr withRightOp(final Expr<? extends Type> rightOp);
}
