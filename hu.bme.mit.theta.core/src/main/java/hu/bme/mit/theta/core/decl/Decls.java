package hu.bme.mit.theta.core.decl;

import java.util.List;

import hu.bme.mit.theta.core.type.Type;

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

	public static <R extends Type> ProcDecl<R> Proc(final String name,
			final List<? extends ParamDecl<? extends Type>> paramDecls, final R returnType) {
		return new ProcDecl<>(name, paramDecls, returnType);
	}

}
