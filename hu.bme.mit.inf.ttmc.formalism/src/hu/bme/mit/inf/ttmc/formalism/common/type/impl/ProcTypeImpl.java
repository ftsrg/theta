package hu.bme.mit.inf.ttmc.formalism.common.type.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.Optional;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;
import hu.bme.mit.inf.ttmc.formalism.common.type.visitor.ProcTypeVisitor;

public class ProcTypeImpl<ReturnType extends Type> implements ProcType<ReturnType> {

	private static final int HASH_SEED = 2069;

	private static final String TYPE_LABEL = "Proc";

	private final ImmutableList<? extends Type> paramTypes;
	private final ReturnType returnType;

	private volatile int hashCode = 0;

	public ProcTypeImpl(final List<? extends Type> paramTypes, final ReturnType returnType) {
		this.paramTypes = ImmutableList.copyOf(checkNotNull(paramTypes));
		this.returnType = checkNotNull(returnType);
	}

	@Override
	public final List<? extends Type> getParamTypes() {
		return paramTypes;
	}

	@Override
	public final ReturnType getReturnType() {
		return returnType;
	}

	@Override
	public final Expr<ProcType<ReturnType>> getAny() {
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
	public final <P, R> R accept(final TypeVisitor<? super P, ? extends R> visitor, final P param) {
		if (visitor instanceof ProcTypeVisitor<?, ?>) {
			final ProcTypeVisitor<? super P, ? extends R> sVisitor = (ProcTypeVisitor<? super P, ? extends R>) visitor;
			return sVisitor.visit(this, param);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public final int hashCode() {
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
	public final String toString() {
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
