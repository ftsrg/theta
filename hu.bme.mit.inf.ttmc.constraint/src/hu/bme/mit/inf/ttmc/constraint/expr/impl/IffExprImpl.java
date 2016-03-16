
package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractIffExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public final class IffExprImpl extends AbstractIffExpr {

	public IffExprImpl(final ConstraintManager manager, final Expr<? extends BoolType> leftOp,
			final Expr<? extends BoolType> rightOp) {
		super(manager, leftOp, rightOp);
	}

}
