package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.IteExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractIteExpr<ExprType extends Type> extends AbstractExpr<ExprType>
		implements IteExpr<ExprType> {

	private static final int HASH_SEED = 181;

	private static final String OPERATOR_LABEL = "Ite";

	private final Expr<? extends BoolType> cond;
	private final Expr<? extends ExprType> then;
	private final Expr<? extends ExprType> elze;

	private volatile int hashCode = 0;

	public AbstractIteExpr(final ConstraintManager manager, final Expr<? extends BoolType> cond,
			final Expr<? extends ExprType> then, final Expr<? extends ExprType> elze) {
		this.cond = checkNotNull(cond);
		this.then = checkNotNull(then);
		this.elze = checkNotNull(elze);
	}

	@Override
	public final Expr<? extends BoolType> getCond() {
		return cond;
	}

	@Override
	public final Expr<? extends ExprType> getThen() {
		return then;
	}

	@Override
	public final Expr<? extends ExprType> getElse() {
		return elze;
	}

	@Override
	public final IteExpr<ExprType> withOps(final Expr<? extends BoolType> cond, final Expr<? extends ExprType> then,
			final Expr<? extends ExprType> elze) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final IteExpr<ExprType> withCond(final Expr<? extends BoolType> cond) {
		return withOps(cond, getThen(), getElse());
	}

	@Override
	public final IteExpr<ExprType> withThen(final Expr<? extends ExprType> then) {
		return withOps(getCond(), then, getElse());
	}

	@Override
	public final IteExpr<ExprType> withElse(final Expr<? extends ExprType> elze) {
		return withOps(getCond(), getThen(), elze);
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final int hashCode() {
		if (hashCode == 0) {
			hashCode = HASH_SEED;
			hashCode = 31 * hashCode + cond.hashCode();
			hashCode = 31 * hashCode + then.hashCode();
			hashCode = 31 * hashCode + elze.hashCode();
		}

		return hashCode;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IteExpr<?>) {
			final IteExpr<?> that = (IteExpr<?>) obj;
			return this.getCond().equals(that.getCond()) && this.getThen().equals(that.getThen())
					&& this.getElse().equals(that.getElse());
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(OPERATOR_LABEL);
		sb.append("(");
		sb.append(getCond().toString());
		sb.append(", ");
		sb.append(getThen().toString());
		sb.append(", ");
		sb.append(getElse().toString());
		sb.append(")");
		return sb.toString();
	}

}
