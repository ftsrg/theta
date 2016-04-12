package hu.bme.mit.inf.ttmc.core.factory.impl;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.decl.impl.Decls;
import hu.bme.mit.inf.ttmc.core.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.core.type.Type;

public class DeclFactoryImpl implements DeclFactory {

	@Override
	public <T extends Type> ConstDecl<T> Const(final String name, final T type) {
		return Decls.Const(name, type);
	}

	@Override
	public <T extends Type> ParamDecl<T> Param(final String name, final T type) {
		return Decls.Param(name, type);
	}

}
