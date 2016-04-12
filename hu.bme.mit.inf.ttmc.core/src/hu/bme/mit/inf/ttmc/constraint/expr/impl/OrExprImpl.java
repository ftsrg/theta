package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.OrExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.impl.Types;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

final class OrExprImpl extends AbstractMultiaryExpr<BoolType, BoolType> implements OrExpr {

	private static final int HASH_SEED = 131;

	private static final String OPERATOR_LABEL = "Or";

	OrExprImpl(final Collection<? extends Expr<? extends BoolType>> ops) {
		super(ImmutableSet.copyOf(checkNotNull(ops)));
	}

	@Override
	public BoolType getType() {
		return Types.Bool();
	}

	@Override
	public OrExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return Exprs.Or(ops);
		}
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof OrExpr) {
			final OrExpr that = (OrExpr) obj;
			return this.getOps().equals(that.getOps());
		} else {
			return false;
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
