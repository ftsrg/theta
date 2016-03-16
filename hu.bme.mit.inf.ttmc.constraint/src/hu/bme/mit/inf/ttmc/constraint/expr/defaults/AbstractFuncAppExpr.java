package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractFuncAppExpr<ParamType extends Type, ResultType extends Type>
		extends AbstractExpr<ResultType> implements FuncAppExpr<ParamType, ResultType> {

	private static final int HASH_SEED = 7951;

	private static final String OPERATOR_LABEL = "App";

	private final Expr<? extends FuncType<? super ParamType, ? extends ResultType>> func;
	private final Expr<? extends ParamType> param;

	private volatile int hashCode = 0;

	public AbstractFuncAppExpr(final ConstraintManager manager,
			final Expr<? extends FuncType<? super ParamType, ? extends ResultType>> func,
			final Expr<? extends ParamType> param) {
		this.func = checkNotNull(func);
		this.param = checkNotNull(param);
	}

	@Override
	public final Expr<? extends FuncType<? super ParamType, ? extends ResultType>> getFunc() {
		return func;
	}

	@Override
	public final Expr<? extends ParamType> getParam() {
		return param;
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final int hashCode() {
		if (hashCode == 0) {
			hashCode = HASH_SEED;
			hashCode = 31 * hashCode + func.hashCode();
			hashCode = 31 * hashCode + param.hashCode();
		}

		return hashCode;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FuncAppExpr<?, ?>) {
			final FuncAppExpr<?, ?> that = (FuncAppExpr<?, ?>) obj;
			return this.getFunc().equals(that.getFunc()) && this.getParam().equals(that.getParam());
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(OPERATOR_LABEL);
		sb.append(func);
		sb.append(", ");
		sb.append(param);
		sb.append(")");
		return sb.toString();
	}

}
