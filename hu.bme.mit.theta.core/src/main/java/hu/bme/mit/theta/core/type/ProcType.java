package hu.bme.mit.theta.core.type;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.Optional;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.utils.TypeVisitor;

public final class ProcType<ReturnType extends Type> implements Type {

	private static final int HASH_SEED = 2069;
	private static final String TYPE_LABEL = "Proc";

	private final ImmutableList<? extends Type> paramTypes;
	private final ReturnType returnType;

	private volatile int hashCode = 0;

	public ProcType(final List<? extends Type> paramTypes, final ReturnType returnType) {
		this.paramTypes = ImmutableList.copyOf(checkNotNull(paramTypes));
		this.returnType = checkNotNull(returnType);
	}

	public List<? extends Type> getParamTypes() {
		return paramTypes;
	}

	public ReturnType getReturnType() {
		return returnType;
	}

	@Override
	public LitExpr<ProcType<ReturnType>> getAny() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isLeq(final Type type) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Optional<? extends Type> meet(final Type type) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Optional<? extends Type> join(final Type type) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <P, R> R accept(final TypeVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + paramTypes.hashCode();
			result = 31 * result + returnType.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ProcType<?>) {
			final ProcType<?> that = (ProcType<?>) obj;
			return this.getParamTypes().equals(that.getParamTypes())
					&& this.getReturnType().equals(that.getReturnType());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final String prefix = TYPE_LABEL + "(";
		sb.append(" -> ");
		sb.append(returnType.toString());
		sb.append(")");
		final String suffix = sb.toString();
		final StringJoiner sj = new StringJoiner(", ", prefix, suffix);
		for (final Type varType : paramTypes) {
			sj.add(varType.toString());
		}
		return sj.toString();
	}

}
