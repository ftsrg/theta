
package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractIffExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public final class IffExprImpl extends AbstractIffExpr {

	public IffExprImpl(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		super(leftOp, rightOp);
	}

}
