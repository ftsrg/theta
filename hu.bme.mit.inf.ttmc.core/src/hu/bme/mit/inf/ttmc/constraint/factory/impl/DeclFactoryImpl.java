package hu.bme.mit.inf.ttmc.constraint.factory.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.impl.Decls;
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

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
