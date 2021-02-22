package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.util.List;
import java.util.Objects;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XstsTypeDeclSymbol implements Symbol {

	private final String name;
	private final List<XstsTypeLiteralSymbol> literals;

	private XstsTypeDeclSymbol(final String name, final List<XstsTypeLiteralSymbol> literals) {
		this.name = checkNotNull(name);
		this.literals = checkNotNull(literals);
	}

	public static XstsTypeDeclSymbol of(final String name, final List<XstsTypeLiteralSymbol> literals) {
		return new XstsTypeDeclSymbol(name, literals);
	}

	@Override
	public int hashCode() {
		return Objects.hash(name);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof XstsTypeDeclSymbol) {
			final XstsTypeDeclSymbol that = (XstsTypeDeclSymbol) obj;
			return this.name.equals(that.name);
		} else {
			return false;
		}
	}

	public String getName() {
		return name;
	}

	public List<XstsTypeLiteralSymbol> getLiterals() {
		return literals;
	}

	@Override
	public String toString() {
		return name + " " + literals;
	}

	public Type instantiate(){
		return IntType.getInstance();
	}
}
