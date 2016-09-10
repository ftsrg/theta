package hu.bme.mit.theta.formalism.common.decl.impl;

import java.util.List;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.common.decl.ProcDecl;
import hu.bme.mit.theta.formalism.common.decl.VarDecl;

public final class Decls2 {

	private Decls2() {
	}

	public static <T extends Type> VarDecl<T> Var(final String name, final T type) {
		return new VarDeclImpl<>(name, type);
	}

	public static ClockDecl Clock(final String name) {
		return new ClockDeclImpl(name);
	}

	public static <R extends Type> ProcDecl<R> Proc(final String name,
			final List<? extends ParamDecl<? extends Type>> paramDecls, final R returnType) {
		return new ProcDeclImpl<>(name, paramDecls, returnType);
	}

}
