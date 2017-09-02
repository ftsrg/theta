package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class LtExpr<OpType extends Ordered<OpType>> extends BinaryExpr<OpType, BoolType> {

	protected LtExpr(final Expr<OpType> leftOp, final Expr<OpType> rightOp) {
		super(leftOp, rightOp);
	}

}
