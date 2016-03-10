package hu.bme.mit.inf.ttmc.constraint.decl.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.impl.AbstractDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class ParamDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType> implements ParamDecl<DeclType> {
	
	public ParamDeclImpl(final String name, final DeclType type) {
		super(name, type);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Param(");
		sb.append(getName());
		sb.append(" : ");
		sb.append(getType());
		sb.append(")");
		return sb.toString();
	}
	
}
