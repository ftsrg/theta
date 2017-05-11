package hu.bme.mit.theta.core.expr;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprVisitor;
import hu.bme.mit.theta.core.utils.impl.TypeUtils;

public final class IteExpr<ExprType extends Type> implements Expr<ExprType> {

	private static final int HASH_SEED = 181;

	private static final String OPERATOR_LABEL = "Ite";

	private final Expr<? extends BoolType> cond;
	private final Expr<? extends ExprType> then;
	private final Expr<? extends ExprType> elze;

	private volatile int hashCode = 0;

	IteExpr(final Expr<? extends BoolType> cond, final Expr<? extends ExprType> then,
			final Expr<? extends ExprType> elze) {

		this.cond = checkNotNull(cond);
		this.then = checkNotNull(then);
		this.elze = checkNotNull(elze);
	}

	public Expr<? extends BoolType> getCond() {
		return cond;
	}

	public Expr<? extends ExprType> getThen() {
		return then;
	}

	public Expr<? extends ExprType> getElse() {
		return elze;
	}

	@Override
	public ExprType getType() {
		final ExprType thenType = getThen().getType();
		final ExprType elseType = getElse().getType();
		final Optional<ExprType> joinResult = TypeUtils.join(thenType, elseType);
		final ExprType result = joinResult.get();
		return result;
	}

	public IteExpr<ExprType> withOps(final Expr<? extends BoolType> cond, final Expr<? extends ExprType> then,
			final Expr<? extends ExprType> elze) {
		if (this.cond == cond && this.then == then && this.elze == elze) {
			return this;
		} else {
			return Exprs.Ite(cond, then, elze);
		}
	}

	public IteExpr<ExprType> withCond(final Expr<? extends BoolType> cond) {
		return withOps(cond, getThen(), getElse());
	}

	public IteExpr<ExprType> withThen(final Expr<? extends ExprType> then) {
		return withOps(getCond(), then, getElse());
	}

	public IteExpr<ExprType> withElse(final Expr<? extends ExprType> elze) {
		return withOps(getCond(), getThen(), elze);
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + cond.hashCode();
			result = 31 * result + then.hashCode();
			result = 31 * result + elze.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IteExpr) {
			final IteExpr<?> that = (IteExpr<?>) obj;
			return this.getCond().equals(that.getCond()) && this.getThen().equals(that.getThen())
					&& this.getElse().equals(that.getElse());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(OPERATOR_LABEL).add(getCond()).add(getThen()).add(getElse()).toString();
	}

}
