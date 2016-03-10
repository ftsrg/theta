package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.StringJoiner;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.MultiaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractMultiaryExpr<OpsType extends Type, ExprType extends Type>
		extends AbstractExpr<ExprType> implements MultiaryExpr<OpsType, ExprType> {

	private final Collection<Expr<? extends OpsType>> ops;
	
	private volatile int hashCode = 0;

	protected AbstractMultiaryExpr(final Collection<Expr<? extends OpsType>> ops) {
		this.ops = checkNotNull(ops);
	}

	@Override
	public Collection<? extends Expr<? extends OpsType>> getOps() {
		return ops;
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = getHashSeed();
			hashCode = 31 * hashCode + getOps().hashCode();
		}

		return hashCode;
	}
	
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final AbstractMultiaryExpr<?, ?> that = (AbstractMultiaryExpr<?, ?>) obj;
			return this.ops.equals(that.ops);
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getOperatorString());
		sb.append("(");
		final String prefix = sb.toString();
		final String suffix = ")";
		final StringJoiner sj = new StringJoiner(", ", prefix, suffix);
		for (Expr<? extends OpsType> op : ops) {
			sj.add(op.toString());
		}
		return sj.toString();
	}

	protected abstract String getOperatorString();
}
