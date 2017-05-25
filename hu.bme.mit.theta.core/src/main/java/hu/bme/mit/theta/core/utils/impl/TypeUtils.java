package hu.bme.mit.theta.core.utils.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class TypeUtils {

	private TypeUtils() {
	}

	public static <T extends Type, T1 extends T, T2 extends T> Optional<T> join(final T1 type1, final T2 type2) {
		checkNotNull(type1);
		checkNotNull(type2);

		final Optional<? extends Type> join = type1.join(type2);
		@SuppressWarnings("unchecked")
		final Optional<T> result = (Optional<T>) join;
		return result;
	}

	public static <T extends Type> Decl<T> cast(final Decl<?> decl, final T type) {
		checkNotNull(decl);
		checkNotNull(type);

		if (decl.getType().equals(type)) {
			@SuppressWarnings("unchecked")
			final Decl<T> result = (Decl<T>) type;
			return result;
		} else {
			throw new ClassCastException("The type of declaration " + decl + " is not of type " + type);
		}
	}

	public static <T extends Type> VarDecl<T> cast(final VarDecl<?> decl, final T type) {
		checkNotNull(decl);
		checkNotNull(type);

		if (decl.getType().equals(type)) {
			@SuppressWarnings("unchecked")
			final VarDecl<T> result = (VarDecl<T>) decl;
			return result;
		} else {
			throw new ClassCastException("The type of declaration " + decl + " is not of type " + type);
		}
	}

	public static <T extends Type> Expr<T> cast(final Expr<?> expr, final Class<T> metaType) {
		checkNotNull(expr);
		checkNotNull(metaType);
	
		if (metaType.isInstance(expr.getType())) {
			@SuppressWarnings("unchecked")
			final Expr<T> result = (Expr<T>) expr;
			return result;
		} else {
			throw new ClassCastException("The type of expression " + expr + " is not of type " + metaType.getName());
		}
	}

}
