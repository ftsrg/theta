package hu.bme.mit.theta.core.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.type.Type;

public abstract class AbstractMultiaryExpr<OpsType extends Type, ExprType extends Type> extends AbstractExpr<ExprType>
		implements MultiaryExpr<OpsType, ExprType> {

	private final Collection<Expr<? extends OpsType>> ops;

	private volatile int hashCode = 0;

	protected AbstractMultiaryExpr(final Collection<Expr<? extends OpsType>> ops) {
		this.ops = checkNotNull(ops);
	}

	@Override
	public final Collection<? extends Expr<? extends OpsType>> getOps() {
		return ops;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 31 * result + getOps().hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final String toString() {
		return ObjectUtils.toStringBuilder(getOperatorLabel()).addAll(ops).toString();
	}

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
