package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.BinaryExpr;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class GtExpr<OpType extends Type> extends BinaryExpr<OpType, BoolType> {

	protected GtExpr(final Expr<OpType> leftOp, final Expr<OpType> rightOp) {
		super(leftOp, rightOp);
	}

}
