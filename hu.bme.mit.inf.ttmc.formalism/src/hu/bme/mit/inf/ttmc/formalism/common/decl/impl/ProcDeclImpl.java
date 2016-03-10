package hu.bme.mit.inf.ttmc.formalism.common.decl.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;

public class ProcDeclImpl<ReturnType extends Type> implements ProcDecl<ReturnType> {

	private final String name;
	private final List<ParamDecl<? extends Type>> paramDecls;
	private final ReturnType returnType;
	
	public ProcDeclImpl(final String name, final List<? extends ParamDecl<? extends Type>> paramDecls, final ReturnType returnType) {
		this.name = checkNotNull(name);
		this.paramDecls = ImmutableList.copyOf(checkNotNull(paramDecls));
		this.returnType = checkNotNull(returnType);
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
	public ProcType<ReturnType> getType() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}
	
	@Override
	public String toString() {
		final String prefix = "proc " + name + "(";
		final String suffix = ") : " + returnType.toString();
		final StringJoiner sj = new StringJoiner(", ", prefix, suffix);
		for (ParamDecl<?> paramDecl : paramDecls) {
			sj.add(paramDecl.toString());
		}
		return sj.toString();
	}
	
}
