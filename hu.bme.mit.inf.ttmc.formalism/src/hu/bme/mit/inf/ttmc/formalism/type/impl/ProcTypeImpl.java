package hu.bme.mit.inf.ttmc.formalism.type.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.type.ProcType;

public class ProcTypeImpl<ReturnType extends Type> implements ProcType<ReturnType> {
	
	private final ImmutableList<? extends Type> paramTypes;
	private final ReturnType returnType;
	
	public ProcTypeImpl(final List<? extends Type> paramTypes, final ReturnType returnType) {
		this.paramTypes = ImmutableList.copyOf(checkNotNull(paramTypes));
		this.returnType = checkNotNull(returnType);
	}
	
	@Override
	public List<? extends Type> getParamTypes() {
		return paramTypes;
	}

	@Override
	public ReturnType getReturnType() {
		return returnType;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final String prefix = "Proc(";
		sb.append(" -> ");
		sb.append(returnType.toString());
		sb.append(")");
		final String suffix = sb.toString();
		final StringJoiner sj = new StringJoiner(", ", prefix, suffix);
		for (Type varType : paramTypes) {
			sj.add(varType.toString());
		}
		return sj.toString();
	}
}
