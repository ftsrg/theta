package hu.bme.mit.inf.ttmc.constraint.decl.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.impl.AbstractDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class ConstDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType> implements ConstDecl<DeclType> {
	
	public ConstDeclImpl(final String name, final DeclType type) {
		super(name, type);
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Const(");
		sb.append(getName());
		sb.append(" : ");
		sb.append(getType());
		sb.append(")");
		return sb.toString();
	}
	
}
