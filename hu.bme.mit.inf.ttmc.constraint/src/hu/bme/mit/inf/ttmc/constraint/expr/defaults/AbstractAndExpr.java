package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractAndExpr extends AbstractMultiaryExpr<BoolType, BoolType> implements AndExpr {

	private static final int HASH_SEED = 41;

	private static final String OPERATOR_LABEL = "And";

	private final ConstraintManager manager;

	public AbstractAndExpr(final ConstraintManager manager, final Collection<? extends Expr<? extends BoolType>> ops) {
		super(ImmutableSet.copyOf(checkNotNull(ops)));
		this.manager = manager;
	}

	@Override
	public final BoolType getType() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final AndExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return manager.getExprFactory().And(ops);
		}
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof AndExpr) {
			final AndExpr that = (AndExpr) obj;
			return this.getOps().equals(that.getOps());
		} else {
			return false;
		}
	}

	@Override
	protected final String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

	@Override
	protected final int getHashSeed() {
		return HASH_SEED;
	}

}
