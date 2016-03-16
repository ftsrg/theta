package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractFuncType<ParamType extends Type, ResultType extends Type> extends AbstractType
		implements FuncType<ParamType, ResultType> {

	private final static int HASH_SEED = 3931;

	private volatile int hashCode = 0;

	private final ParamType paramType;
	private final ResultType resultType;

	public AbstractFuncType(final ParamType paramType, final ResultType resultType) {
		this.paramType = checkNotNull(paramType);
		this.resultType = checkNotNull(resultType);
	}

	@Override
	public ParamType getParamType() {
		return paramType;
	}

	@Override
	public ResultType getResultType() {
		return resultType;
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = HASH_SEED;
			hashCode = 31 * hashCode + paramType.hashCode();
			hashCode = 31 * hashCode + resultType.hashCode();
		}

		return hashCode;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FuncType<?, ?>) {
			final FuncType<?, ?> that = (FuncType<?, ?>) obj;
			return this.getParamType().equals(that.getParamType()) && this.getResultType().equals(that.getResultType());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Func(");
		sb.append(paramType);
		sb.append(" -> ");
		sb.append(resultType);
		sb.append(")");
		return sb.toString();
	}

}
