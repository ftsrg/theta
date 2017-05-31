package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class EqExpr<OpType extends Type> extends BinaryExpr<OpType, OpType, BoolType> {

	protected EqExpr(final Expr<? extends OpType> leftOp, final Expr<? extends OpType> rightOp) {
		super(leftOp, rightOp);
	}

}
