package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractModExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public final class ModExprImpl extends AbstractModExpr {

	public ModExprImpl(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		super(leftOp, rightOp);
	}

}