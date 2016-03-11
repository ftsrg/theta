package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableMultiset;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractAddExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;

public final class AddExprImpl<ExprType extends ClosedUnderAdd> extends AbstractAddExpr<ExprType> {

	public AddExprImpl(final Collection<? extends Expr<? extends ExprType>> ops) {
		super(ImmutableMultiset.copyOf(checkNotNull(ops)));
	}

}
