package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeVisitor;

public abstract class AbstractFuncType<ParamType extends Type, ResultType extends Type> extends AbstractType
		implements FuncType<ParamType, ResultType> {

	private final static int HASH_SEED = 3931;

	private final static String TYPE_LABEL = "Func";

	private final ConstraintManager manager;

	private final ParamType paramType;
	private final ResultType resultType;

	private volatile int hashCode = 0;

	public AbstractFuncType(final ConstraintManager manager, final ParamType paramType, final ResultType resultType) {
		this.paramType = checkNotNull(paramType);
		this.resultType = checkNotNull(resultType);
		this.manager = manager;
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
	public final Expr<FuncType<ParamType, ResultType>> getAny() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final boolean isLeq(final Type type) {
		if (type instanceof AbstractFuncType<?, ?>) {
			final AbstractFuncType<?, ?> that = (AbstractFuncType<?, ?>) type;
			return that.paramType.isLeq(this.paramType) && this.resultType.isLeq(that.resultType);
		} else {
			return false;
		}
	}

	@Override
	public final Optional<FuncType<?, ?>> meet(final Type type) {
		if (type instanceof FuncType<?, ?>) {
			final FuncType<?, ?> that = (FuncType<?, ?>) type;
			final Optional<? extends Type> joinOfParamTypes = this.getParamType().join(that.getParamType());
			final Optional<? extends Type> meetOfResultTypes = this.getResultType().meet(that.getResultType());

			if (joinOfParamTypes.isPresent() && meetOfResultTypes.isPresent()) {
				final FuncType<?, ?> funcType = manager.getTypeFactory().Func(joinOfParamTypes.get(),
						meetOfResultTypes.get());
				return Optional.of(funcType);
			}
		}

		return Optional.empty();
	}

	@Override
	public final Optional<FuncType<?, ?>> join(final Type type) {
		if (type instanceof FuncType<?, ?>) {
			final FuncType<?, ?> that = (FuncType<?, ?>) type;
			final Optional<? extends Type> meetOfParamTypes = this.getParamType().meet(that.getParamType());
			final Optional<? extends Type> joinOfResultTypes = this.getResultType().join(that.getResultType());

			if (meetOfParamTypes.isPresent() && joinOfResultTypes.isPresent()) {
				final FuncType<?, ?> funcType = manager.getTypeFactory().Func(meetOfParamTypes.get(),
						joinOfResultTypes.get());
				return Optional.of(funcType);
			}
		}

		return Optional.empty();
	}

	@Override
	public final <P, R> R accept(final TypeVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + paramType.hashCode();
			result = 31 * result + resultType.hashCode();
			hashCode = result;
		}
		return result;
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
