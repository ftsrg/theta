package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.core.Type;

public final class Decls {

	private Decls() {
	}

	public static <T extends Type> ConstDecl<T> Const(final String name, final T type) {
		return new SimpleConstDecl<>(name, type);
	}

	public static <T extends Type> ParamDecl<T> Param(final String name, final T type) {
		return new ParamDecl<>(name, type);
	}

	public static <T extends Type> VarDecl<T> Var(final String name, final T type) {
		return new VarDecl<>(name, type);
	}

}
