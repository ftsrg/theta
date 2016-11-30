package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;

public interface EqExpr extends BinaryExpr<Type, Type, BoolType> {

	@Override
	EqExpr withOps(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp);

	@Override
	EqExpr withLeftOp(final Expr<? extends Type> leftOp);

	@Override
	EqExpr withRightOp(final Expr<? extends Type> rightOp);

}
