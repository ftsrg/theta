package hu.bme.mit.inf.ttmc.constraint.decl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class Decls {

	protected Decls() {
	}

	public static <T extends Type> ConstDecl<T> Const(final String name, final T type) {
		checkNotNull(name);
		checkNotNull(type);
		checkArgument(name.length() > 0);
		return new ConstDeclImpl<>(name, type);
	}

	public static <T extends Type> ParamDecl<T> Param(final String name, final T type) {
		checkNotNull(name);
		checkNotNull(type);
		checkArgument(name.length() > 0);
		return new ParamDeclImpl<T>(name, type);
	}

}
