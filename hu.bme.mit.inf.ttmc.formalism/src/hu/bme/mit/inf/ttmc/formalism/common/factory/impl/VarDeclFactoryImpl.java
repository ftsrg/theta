package hu.bme.mit.inf.ttmc.formalism.common.factory.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.impl.VarDeclImpl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;

public class VarDeclFactoryImpl extends DeclFactoryDecorator implements VarDeclFactory {

	public VarDeclFactoryImpl(final DeclFactory factory) {
		super(factory);
	}

	@Override
	public <T extends Type> VarDecl<T> Var(final String name, final T type) {
		checkNotNull(name);
		checkNotNull(type);
		checkArgument(name.length() > 0);

		final VarDecl<T> varDecl = new VarDeclImpl<>(name, type);
		return varDecl;
	}

}
