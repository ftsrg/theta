package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractMulExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;

public final class MulExprImpl<ExprType extends ClosedUnderMul> extends AbstractMulExpr<ExprType> {

	public MulExprImpl(final ConstraintManager manager, final Collection<? extends Expr<? extends ExprType>> ops) {
		super(manager, ops);
	}

}
