package hu.bme.mit.theta.core.type.functype;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class FuncAppExpr<ParamType extends Type, ResultType extends Type> implements Expr<ResultType> {

	private static final int HASH_SEED = 7951;

	private static final String OPERATOR_LABEL = "App";

	private final Expr<FuncType<ParamType, ResultType>> func;
	private final Expr<ParamType> param;

	private volatile int hashCode = 0;

	FuncAppExpr(final Expr<FuncType<ParamType, ResultType>> func, final Expr<ParamType> param) {
		this.func = checkNotNull(func);
		this.param = checkNotNull(param);
	}

	public Expr<FuncType<ParamType, ResultType>> getFunc() {
		return func;
	}

	public Expr<ParamType> getParam() {
		return param;
	}

	@Override
	public ResultType getType() {
		return getFunc().getType().getResultType();
	}

	@Override
	public int getArity() {
		return 2;
	}

	@Override
	public List<Expr<?>> getOps() {
		return ImmutableList.of(func, param);
	}

	@Override
	public Expr<ResultType> withOps(final List<? extends Expr<?>> ops) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public FuncAppExpr<ParamType, ResultType> with(final Expr<FuncType<ParamType, ResultType>> func,
			final Expr<ParamType> param) {
		if (this.func == func && this.param == param) {
			return this;
		} else {
			return new FuncAppExpr<>(func, param);
		}
	}

	public FuncAppExpr<ParamType, ResultType> withFunc(final Expr<FuncType<ParamType, ResultType>> func) {
		return with(func, getParam());
	}

	public FuncAppExpr<ParamType, ResultType> withParam(final Expr<ParamType> param) {
		return with(getFunc(), param);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + func.hashCode();
			result = 31 * result + param.hashCode();
			hashCode = result;
		}
		return result;
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
	public String toString() {
		return ObjectUtils.toStringBuilder(OPERATOR_LABEL).add(func).add(param).toString();
	}

}
