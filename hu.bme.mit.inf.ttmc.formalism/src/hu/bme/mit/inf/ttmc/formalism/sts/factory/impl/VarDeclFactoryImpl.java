package hu.bme.mit.inf.ttmc.formalism.sts.factory.impl;

import hu.bme.mit.inf.ttmc.core.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.VarDeclFactory;

public class VarDeclFactoryImpl extends DeclFactoryDecorator implements VarDeclFactory {

	public VarDeclFactoryImpl(final DeclFactory factory) {
		super(factory);
	}

	@Override
	public <T extends Type> VarDecl<T> Var(final String name, final T type) {
		return Decls2.Var(name, type);
	}

}
