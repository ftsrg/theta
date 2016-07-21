package hu.bme.mit.inf.ttmc.formalism.common.decl.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.DeclVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;

final class ProcDeclImpl<ReturnType extends Type> implements ProcDecl<ReturnType> {

	private static final int HASH_SEED = 4001;

	private final String name;
	private final List<ParamDecl<? extends Type>> paramDecls;
	private final ReturnType returnType;

	private final ProcRefExpr<ReturnType> ref;

	private volatile int hashCode;

	ProcDeclImpl(final String name, final List<? extends ParamDecl<? extends Type>> paramDecls,
			final ReturnType returnType) {
		this.name = checkNotNull(name);
		this.paramDecls = ImmutableList.copyOf(checkNotNull(paramDecls));
		this.returnType = checkNotNull(returnType);
		ref = new ProcRefExprImpl<>(this);
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
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
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
			result = 31 * result + getType().hashCode();
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
