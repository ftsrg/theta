package hu.bme.mit.theta.core.decl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.Type;

public final class SimpleConstDecl<DeclType extends Type> extends ConstDecl<DeclType> {

	private final String name;
	private final DeclType type;

	public SimpleConstDecl(final String name, final DeclType type) {
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

}
