package hu.bme.mit.inf.ttmc.formalism.common.factory.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class DeclFactoryDecorator implements DeclFactory {

	private final DeclFactory factory;
	
	public DeclFactoryDecorator(final DeclFactory factory) {
		checkNotNull(factory);
		this.factory = factory;
	}
	
	@Override
	public <T extends Type> ConstDecl<T> Const(String name, T type) {
		return factory.Const(name, type);
	}

	@Override
	public <T extends Type> ParamDecl<T> Param(String name, T type) {
		return factory.Param(name, type);
	}

}
