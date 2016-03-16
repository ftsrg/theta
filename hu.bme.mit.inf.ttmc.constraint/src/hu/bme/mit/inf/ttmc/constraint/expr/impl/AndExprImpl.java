package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractAndExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public final class AndExprImpl extends AbstractAndExpr {

	public AndExprImpl(final ConstraintManager manager, final Collection<? extends Expr<? extends BoolType>> ops) {
		super(manager, ImmutableSet.copyOf(checkNotNull(ops)));
	}

}
