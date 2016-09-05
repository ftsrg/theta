package hu.bme.mit.inf.theta.common.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Optional;
import java.util.StringJoiner;

public final class SymbolTable {

	private final LinkedHashMap<String, Symbol> stringToSymbol;

	public SymbolTable() {
		stringToSymbol = new LinkedHashMap<>();
	}

	////

	public void add(final Symbol symbol) {
		checkNotNull(symbol);
		checkArgument(!stringToSymbol.containsKey(symbol.getName()));
		stringToSymbol.put(symbol.getName(), symbol);
	}

	public void addAll(final Collection<? extends Symbol> symbols) {
		checkNotNull(symbols);
		for (final Symbol symbol : symbols) {
			add(symbol);
		}
	}

	public Optional<Symbol> get(final String name) {
		final Symbol symbol = stringToSymbol.get(name);
		return Optional.ofNullable(symbol);
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "SymbolTable(", ")");
		for (final Symbol symbol : stringToSymbol.values()) {
			sj.add(symbol.toString());
		}
		return sj.toString();
	}

}
