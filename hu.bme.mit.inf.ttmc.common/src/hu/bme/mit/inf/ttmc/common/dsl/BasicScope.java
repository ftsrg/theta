package hu.bme.mit.inf.ttmc.common.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

public abstract class BasicScope implements Scope {

	final Optional<Scope> enclosingScope;
	final Map<String, Symbol> stringToSymbol;

	public BasicScope(final Scope eclosingScope) {
		this.enclosingScope = Optional.ofNullable(eclosingScope);
		stringToSymbol = new HashMap<>();
	}

	@Override
	public Optional<Scope> getEnclosingScope() {
		return enclosingScope;
	}

	@Override
	public Optional<Symbol> resolve(final String name) {
		checkNotNull(name);
		final Symbol symbol = stringToSymbol.get(name);
		if (symbol != null) {
			return Optional.of(symbol);
		} else if (enclosingScope.isPresent()) {
			return enclosingScope.get().resolve(name);
		} else {
			return Optional.empty();
		}
	}

	@Override
	public void declare(final Symbol symbol) {
		checkNotNull(symbol);
		checkArgument(!stringToSymbol.containsKey(symbol.getName()));
		stringToSymbol.put(symbol.getName(), symbol);
	}

}
