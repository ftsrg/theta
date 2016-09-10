package hu.bme.mit.theta.core.decl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Type;

public final class Decls {

	private Decls() {
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
