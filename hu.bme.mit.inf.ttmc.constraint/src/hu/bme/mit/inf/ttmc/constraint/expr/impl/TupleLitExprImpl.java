package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.TupleLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractMultiaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.TupleType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class TupleLitExprImpl
		extends AbstractMultiaryExpr<Type, TupleType> implements TupleLitExpr {

	private static final String OPERATOR = "Tuple";

	public TupleLitExprImpl(final ConstraintManager manager,
			final Collection<? extends Expr<? extends Type>> ops) {
		super(ImmutableList.copyOf(checkNotNull(ops)));
	}
	
	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected int getHashSeed() {
		return 173;
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
