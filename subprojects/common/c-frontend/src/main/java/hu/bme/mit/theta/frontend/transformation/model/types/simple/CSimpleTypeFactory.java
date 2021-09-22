package hu.bme.mit.theta.frontend.transformation.model.types.simple;

import hu.bme.mit.theta.core.type.Expr;

import java.util.Map;
import java.util.Optional;

public class CSimpleTypeFactory {

	public static Unsigned Unsigned() { return Unsigned.instance; }

	public static Signed Signed() { return Signed.instance; }

	public static Volatile Volatile() {
		return Volatile.instance;
	}

	public static Atomic Atomic() {
		return Atomic.instance;
	}

	public static Extern Extern() { return Extern.instance; }

	public static Typedef Typedef() { return Typedef.instance; }

	public static NamedType NamedType(final String namedType) { return new NamedType(namedType); }

	public static DeclaredName DeclaredName(final String declaredName) { return new DeclaredName(declaredName); }

	public static Enum Enum(final String id, final Map<String, Optional<Expr<?>>> fields) { return new Enum(id, fields); }

	public static Struct Struct(final String name) { return new Struct(name); }

	public static ThreadLocal ThreadLocal() { return ThreadLocal.instance; }
}
