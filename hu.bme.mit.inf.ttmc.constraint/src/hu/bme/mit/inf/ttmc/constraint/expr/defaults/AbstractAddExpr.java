package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.stream.Stream;

import com.google.common.collect.ImmutableMultiset;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.AddExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeUtils;

public abstract class AbstractAddExpr<ExprType extends ClosedUnderAdd> extends AbstractMultiaryExpr<ExprType, ExprType>
		implements AddExpr<ExprType> {

	private static final int HASH_SEED = 73;

	private static final String OPERATOR_LABEL = "Add";

	private final ConstraintManager manager;

	public AbstractAddExpr(final ConstraintManager manager, final Collection<? extends Expr<? extends ExprType>> ops) {
		super(ImmutableMultiset.copyOf(checkNotNull(ops)));
		this.manager = manager;
	}

	@Override
	public final ExprType getType() {
		checkArgument(getOps().size() > 0);
		final ExprType headType = getOps().iterator().next().getType();
		final Stream<ExprType> tailTypes = getOps().stream().skip(1).map(e -> (ExprType) e.getType());
		final ExprType result = tailTypes.reduce(headType, (t1, t2) -> TypeUtils.join(t1, t2).get());
		return result;
	}

	@Override
	public final AddExpr<ExprType> withOps(final Collection<? extends Expr<? extends ExprType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return manager.getExprFactory().Add(ops);
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
		} else if (obj instanceof AddExpr<?>) {
			final AddExpr<?> that = (AddExpr<?>) obj;
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
