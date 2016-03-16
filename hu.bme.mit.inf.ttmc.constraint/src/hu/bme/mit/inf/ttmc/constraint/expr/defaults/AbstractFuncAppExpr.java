package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractFuncAppExpr<ParamType extends Type, ResultType extends Type>
		extends AbstractExpr<ResultType> implements FuncAppExpr<ParamType, ResultType> {

	private final Expr<? extends FuncType<? super ParamType, ? extends ResultType>> func;
	private final Expr<? extends ParamType> param;

	private static final int HASH_SEED = 47;

	private volatile int hashCode = 0;

	public AbstractFuncAppExpr(final Expr<? extends FuncType<? super ParamType, ? extends ResultType>> func,
			final Expr<? extends ParamType> param) {
		this.func = checkNotNull(func);
		this.param = checkNotNull(param);
	}

	@Override
	public Expr<? extends FuncType<? super ParamType, ? extends ResultType>> getFunc() {
		return func;
	}

	@Override
	public Expr<? extends ParamType> getParam() {
		return param;
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = HASH_SEED;
			hashCode = 31 * hashCode + func.hashCode();
			hashCode = 31 * hashCode + param.hashCode();
		}

		return hashCode;
	}

	@Override
	public boolean equals(final Object obj) {
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
		sb.append("App(");
		sb.append(func);
		sb.append(", ");
		sb.append(param);
		sb.append(")");
		return sb.toString();
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}
}
