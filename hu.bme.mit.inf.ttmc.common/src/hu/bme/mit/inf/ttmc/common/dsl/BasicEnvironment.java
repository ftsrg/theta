package hu.bme.mit.inf.ttmc.common.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

public final class BasicEnvironment implements Environment {

	private final Optional<Environment> enclosingEnvironment;
	private final Map<Symbol, Object> symbolToDef;

	public BasicEnvironment(final Environment enclosingEnvironment) {
		this.enclosingEnvironment = Optional.ofNullable(enclosingEnvironment);
		symbolToDef = new HashMap<>();
	}

	@Override
	public Optional<Object> valuation(final Symbol symbol) {
		checkNotNull(symbol);
		final Object value = symbolToDef.get(symbol);
		if (value != null || !enclosingEnvironment.isPresent()) {
			return Optional.ofNullable(value);
		} else {
			return enclosingEnvironment.get().valuation(symbol);
		}
	}

	@Override
	public void define(final Symbol symbol, final Object value) {
		checkNotNull(symbol);
		checkNotNull(value);
		checkArgument(!symbolToDef.containsKey(symbol));
		symbolToDef.put(symbol, value);
	}

	@Override
	public void defineAll(final List<? extends Symbol> symbols, final List<? extends Object> values) {
		checkNotNull(symbols);
		checkNotNull(values);
		checkArgument(symbols.size() == values.size());
		for (int i = 0; i < symbols.size(); i++) {
			final Symbol symbol = symbols.get(i);
			final Object value = values.get(i);
			define(symbol, value);
		}
	}

	@Override
	public Optional<Environment> enclosingEnvironment() {
		return enclosingEnvironment;
	}

}
