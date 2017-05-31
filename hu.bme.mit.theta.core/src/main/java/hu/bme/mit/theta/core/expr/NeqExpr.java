package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class NeqExpr<OpType extends Type> extends BinaryExpr<OpType, OpType, BoolType> {

	protected NeqExpr(final Expr<? extends OpType> leftOp, final Expr<? extends OpType> rightOp) {
		super(leftOp, rightOp);
	}

}
