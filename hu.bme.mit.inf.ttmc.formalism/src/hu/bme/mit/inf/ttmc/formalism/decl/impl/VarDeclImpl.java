package hu.bme.mit.inf.ttmc.formalism.decl.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl;

public class VarDeclImpl<DeclType extends Type> implements VarDecl<DeclType> {

	private final String name;
	private final DeclType type;
		
	public VarDeclImpl(final String name, final DeclType type) {
		this.name = checkNotNull(name);
		this.type = checkNotNull(type);
	}
	
	@Override
	public String getName() {
		return name;
	}

	@Override
	public DeclType getType() {
		return type;
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
