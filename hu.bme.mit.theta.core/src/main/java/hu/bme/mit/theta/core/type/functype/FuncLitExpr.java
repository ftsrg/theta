package hu.bme.mit.theta.core.type.functype;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.utils.TypeUtils;

public final class FuncLitExpr<ParamType extends Type, ResultType extends Type>
		implements LitExpr<FuncType<ParamType, ResultType>> {

	private static final int HASH_SEED = 53;
	private static final String OPERATOR_LABEL = "Func";

	private final ParamDecl<ParamType> param;
	private final Expr<ResultType> result;

	private volatile int hashCode = 0;

	FuncLitExpr(final ParamDecl<ParamType> param, final Expr<ResultType> result) {
		this.param = checkNotNull(param);
		this.result = checkNotNull(result);
	}

	public ParamDecl<ParamType> getParam() {
		return param;
	}

	public Expr<ResultType> getResult() {
		return result;
	}

	@Override
	public FuncType<ParamType, ResultType> getType() {
		return Func(param.getType(), result.getType());
	}

	@Override
	public LitExpr<FuncType<ParamType, ResultType>> eval(final Assignment assignment) {
		return this;
	}

	@Override
	public int getArity() {
		return 1;
	}

	@Override
	public List<? extends Expr<?>> getOps() {
		return ImmutableList.of(result);
	}

	@Override
	public Expr<FuncType<ParamType, ResultType>> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		checkArgument(ops.size() == 1);
		final Expr<ResultType> newResult = TypeUtils.cast(ops.get(0), result.getType());
		return with(newResult);
	}

	public FuncLitExpr<ParamType, ResultType> with(final Expr<ResultType> result) {
		if (this.result == result) {
			return this;
		} else {
			return new FuncLitExpr<>(param, result);
		}
	}

	@Override
	public int hashCode() {
		int tmp = hashCode;
		if (tmp == 0) {
			tmp = HASH_SEED;
			tmp = 31 * tmp + param.hashCode();
			tmp = 31 * tmp + result.hashCode();
			hashCode = tmp;
		}
		return tmp;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FuncLitExpr) {
			final FuncLitExpr<?, ?> that = (FuncLitExpr<?, ?>) obj;
			return this.getParam().equals(that.getParam()) && this.getResult().equals(that.getResult());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(OPERATOR_LABEL);
		sb.append("(");
		sb.append(param);
		sb.append(" -> ");
		sb.append(result);
		sb.append(")");
		return sb.toString();
	}

}
