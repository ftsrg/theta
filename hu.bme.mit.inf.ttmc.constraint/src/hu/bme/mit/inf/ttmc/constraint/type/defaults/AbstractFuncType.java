package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeVisitor;

public abstract class AbstractFuncType<ParamType extends Type, ResultType extends Type> extends AbstractType
		implements FuncType<ParamType, ResultType> {

	private final static int HASH_SEED = 3931;

	private final static String TYPE_LABEL = "Func";

	private volatile int hashCode = 0;

	private final ParamType paramType;
	private final ResultType resultType;

	public AbstractFuncType(final ParamType paramType, final ResultType resultType) {
		this.paramType = checkNotNull(paramType);
		this.resultType = checkNotNull(resultType);
	}

	@Override
	public final ParamType getParamType() {
		return paramType;
	}

	@Override
	public final ResultType getResultType() {
		return resultType;
	}

	@Override
	public final <P, R> R accept(final TypeVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final int hashCode() {
		if (hashCode == 0) {
			hashCode = HASH_SEED;
			hashCode = 31 * hashCode + paramType.hashCode();
			hashCode = 31 * hashCode + resultType.hashCode();
		}

		return hashCode;
	}

	@Override
	public final boolean equals(final Object obj) {
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
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(TYPE_LABEL);
		sb.append("(");
		sb.append(paramType);
		sb.append(" -> ");
		sb.append(resultType);
		sb.append(")");
		return sb.toString();
	}

}
