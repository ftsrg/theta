package hu.bme.mit.inf.ttmc.formalism.common.decl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public final class Decls2 {

	private Decls2() {
	}

	public static <T extends Type> VarDecl<T> Var(final String name, final T type) {
		checkNotNull(name);
		checkNotNull(type);
		checkArgument(name.length() > 0);
		return new VarDeclImpl<T>(name, type);
	}

	public static <R extends Type> ProcDecl<R> Proc(final String name,
			final List<? extends ParamDecl<? extends Type>> paramDecls, final R returnType) {
		checkNotNull(name);
		checkNotNull(paramDecls);
		checkNotNull(returnType);
		checkArgument(name.length() > 0);
		return new ProcDeclImpl<>(name, paramDecls, returnType);
	}

	public static <R extends Type> ProcDecl<R> Proc(final String name,
			final List<? extends ParamDecl<? extends Type>> paramDecls, final R returnType, final Stmt stmt) {
		checkNotNull(name);
		checkNotNull(paramDecls);
		checkNotNull(returnType);
		checkNotNull(stmt);
		checkArgument(name.length() > 0);
		return new ProcDeclImpl<>(name, paramDecls, returnType, stmt);
	}

}
