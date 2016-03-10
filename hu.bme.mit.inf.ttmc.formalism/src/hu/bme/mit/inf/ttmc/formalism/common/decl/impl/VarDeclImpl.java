package hu.bme.mit.inf.ttmc.formalism.common.decl.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.decl.impl.AbstractDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class VarDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType> implements VarDecl<DeclType> {


	public VarDeclImpl(final String name, final DeclType type) {
		super(name, type);
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("var ");
		sb.append(getName());
		sb.append(" : ");
		sb.append(getType().toString());
		return sb.toString();
	}
}
