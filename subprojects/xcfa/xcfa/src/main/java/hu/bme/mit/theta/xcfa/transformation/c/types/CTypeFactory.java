package hu.bme.mit.theta.xcfa.transformation.c.types;

import hu.bme.mit.theta.core.type.Expr;

import java.util.Map;
import java.util.Optional;

public class CTypeFactory {

	public static Unsigned Unsigned() { return Unsigned.instance; }

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
}
