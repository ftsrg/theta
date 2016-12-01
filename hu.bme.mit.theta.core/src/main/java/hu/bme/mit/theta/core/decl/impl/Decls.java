package hu.bme.mit.theta.core.decl.impl;

import java.util.List;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.ProcDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public final class Decls {

	private Decls() {
	}

	public static <T extends Type> ConstDecl<T> Const(final String name, final T type) {
		return new ConstDeclImpl<>(name, type);
	}

	public static <T extends Type> ParamDecl<T> Param(final String name, final T type) {
		return new ParamDeclImpl<>(name, type);
	}

	public static <T extends Type> VarDecl<T> Var(final String name, final T type) {
		return new VarDeclImpl<>(name, type);
	}

	public static <R extends Type> ProcDecl<R> Proc(final String name,
			final List<? extends ParamDecl<? extends Type>> paramDecls, final R returnType) {
		return new ProcDeclImpl<>(name, paramDecls, returnType);
	}

}
