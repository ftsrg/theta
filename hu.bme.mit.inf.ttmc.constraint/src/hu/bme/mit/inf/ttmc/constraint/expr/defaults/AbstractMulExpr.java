package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableMultiset;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.MulExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractMulExpr<ExprType extends ClosedUnderMul> extends AbstractMultiaryExpr<ExprType, ExprType>
		implements MulExpr<ExprType> {

	private static final int HASH_SEED = 2221;

	private static final String OPERATOR_LABEL = "Mul";

	private final ConstraintManager manager;

	public AbstractMulExpr(final ConstraintManager manager, final Collection<? extends Expr<? extends ExprType>> ops) {
		super(ImmutableMultiset.copyOf(checkNotNull(ops)));
		this.manager = manager;
	}

	@Override
	public final ExprType getType() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final MulExpr<ExprType> withOps(final Collection<? extends Expr<? extends ExprType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return manager.getExprFactory().Mul(ops);
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
		} else if (obj instanceof MulExpr<?>) {
			final MulExpr<?> that = (MulExpr<?>) obj;
			return this.getOps().equals(that.getOps());
		} else {
			return false;
		}
	}

	@Override
	protected final int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected final String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
