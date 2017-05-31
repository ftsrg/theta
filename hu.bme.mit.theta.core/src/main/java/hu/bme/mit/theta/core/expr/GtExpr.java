package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class GtExpr<OpType extends Type> extends BinaryExpr<OpType, OpType, BoolType> {

	protected GtExpr(final Expr<? extends OpType> leftOp, final Expr<? extends OpType> rightOp) {
		super(leftOp, rightOp);
	}

}
