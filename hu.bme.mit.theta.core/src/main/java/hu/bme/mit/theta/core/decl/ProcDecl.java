package hu.bme.mit.theta.core.decl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.proctype.ProcExprs.Proc;
import static java.util.stream.Collectors.toList;

import java.util.List;
import java.util.stream.Stream;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.proctype.ProcType;
import hu.bme.mit.theta.core.utils.DeclVisitor;

public final class ProcDecl<ReturnType extends Type> extends Decl<ProcType<ReturnType>> {

	private final String name;
	private final List<ParamDecl<? extends Type>> paramDecls;
	private final ReturnType returnType;
	private final ProcType<ReturnType> type;

	ProcDecl(final String name, final List<? extends ParamDecl<? extends Type>> paramDecls,
			final ReturnType returnType) {
		checkNotNull(name);
		checkNotNull(paramDecls);
		checkNotNull(returnType);
		checkArgument(name.length() > 0);
		this.name = name;
		this.paramDecls = ImmutableList.copyOf(paramDecls);
		this.returnType = returnType;

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

	public List<? extends ParamDecl<?>> getParamDecls() {
		return paramDecls;
	}

	public ReturnType getReturnType() {
		return returnType;
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
