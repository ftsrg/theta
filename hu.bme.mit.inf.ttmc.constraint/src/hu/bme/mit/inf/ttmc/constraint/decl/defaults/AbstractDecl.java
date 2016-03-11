package hu.bme.mit.inf.ttmc.constraint.decl.defaults;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractDecl<DeclType extends Type> implements Decl<DeclType> {
	
	private final String name;
	private final DeclType type;
	
	
	protected AbstractDecl(final String name, final DeclType type) {
		checkNotNull(name);
		checkArgument(name.length() > 0);
		this.name = name;
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
		
}
