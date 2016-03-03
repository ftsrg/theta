package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.IteExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class IteExprImpl<ExprType extends Type> extends AbstractExpr<ExprType> implements IteExpr<ExprType> {

	private final Expr<? extends BoolType> cond;
	private final Expr<? extends ExprType> then;
	private final Expr<? extends ExprType> elze;

	private volatile int hashCode = 0;

	public IteExprImpl(final Expr<? extends BoolType> cond, final Expr<? extends ExprType> then,
			final Expr<? extends ExprType> elze) {
		this.cond = checkNotNull(cond);
		this.then = checkNotNull(then);
		this.elze = checkNotNull(elze);
	}

	@Override
	public Expr<? extends BoolType> getCond() {
		return cond;
	}

	@Override
	public Expr<? extends ExprType> getThen() {
		return then;
	}

	@Override
	public Expr<? extends ExprType> getElse() {
		return elze;
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = getHashSeed();
			hashCode = 31 * hashCode + cond.hashCode();
			hashCode = 31 * hashCode + then.hashCode();
			hashCode = 31 * hashCode + elze.hashCode();
		}

		return hashCode;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final IteExprImpl<?> that = (IteExprImpl<?>) obj;
			return this.cond.equals(that.cond) && this.then.equals(that.then) && this.elze.equals(that.elze);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Ite");
		sb.append("(");
		sb.append(getCond().toString());
		sb.append(", ");
		sb.append(getThen().toString());
		sb.append(", ");
		sb.append(getElse().toString());
		sb.append(")");
		return sb.toString();
	}

	@Override
	protected int getHashSeed() {
		return 181;
	}

	@Override
	public IteExpr<ExprType> withOps(Expr<? extends BoolType> cond, Expr<? extends ExprType> then,
			Expr<? extends ExprType> elze) {
		return new IteExprImpl<>(cond, then, elze);
	}

}
