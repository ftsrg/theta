package hu.bme.mit.theta.core.decl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.impl.Types.Proc;
import static java.util.stream.Collectors.toList;

import java.util.List;
import java.util.stream.Stream;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.ProcDecl;
import hu.bme.mit.theta.core.expr.ProcRefExpr;
import hu.bme.mit.theta.core.type.ProcType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.DeclVisitor;

final class ProcDeclImpl<ReturnType extends Type> implements ProcDecl<ReturnType> {

	private static final int HASH_SEED = 4001;

	private final String name;
	private final List<ParamDecl<? extends Type>> paramDecls;
	private final ReturnType returnType;

	private final ProcRefExpr<ReturnType> ref;
	private final ProcType<ReturnType> type;

	private volatile int hashCode;

	ProcDeclImpl(final String name, final List<? extends ParamDecl<? extends Type>> paramDecls,
			final ReturnType returnType) {
		checkNotNull(name);
		checkNotNull(paramDecls);
		checkNotNull(returnType);
		checkArgument(name.length() > 0);
		this.name = name;
		this.paramDecls = ImmutableList.copyOf(paramDecls);
		this.returnType = returnType;

		ref = new ProcRefExprImpl<>(this);
		type = createProcType(paramDecls, returnType);
	}

	private static <ReturnType extends Type> ProcType<ReturnType> createProcType(
			final List<? extends ParamDecl<? extends Type>> paramDecls, final ReturnType returnType) {
		final Stream<Type> paramTypeStream = paramDecls.stream().map(p -> p.getType());
		final List<Type> paramTypes = paramTypeStream.collect(toList());
		return Proc(paramTypes, returnType);
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public List<? extends ParamDecl<?>> getParamDecls() {
		return paramDecls;
	}

	@Override
	public ReturnType getReturnType() {
		return returnType;
	}

	@Override
	public ProcRefExpr<ReturnType> getRef() {
		return ref;
	}

	@Override
	public ProcType<ReturnType> getType() {
		return type;
	}

	@Override
	public <P, R> R accept(final DeclVisitor<? super P, ? extends R> visitor, final P param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + getName().hashCode();
			result = 31 * result + getReturnType().hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		return this == obj;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Proc(");
		sb.append(name);
		for (final ParamDecl<?> paramDecl : paramDecls) {
			sb.append(", ");
			sb.append(paramDecl);
		}
		sb.append(" : ");
		sb.append(returnType);
		return sb.toString();
	}

}
