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
			hashCode = getHashSeed();
			hashCode = 31 * hashCode + func.hashCode();
			hashCode = 31 * hashCode + param.hashCode();
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
			final AbstractFuncAppExpr<?, ?> that = (AbstractFuncAppExpr<?, ?>) obj;
			return this.func.equals(that.func) && this.param.equals(that.param);
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
	protected int getHashSeed() {
		return 47;
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
