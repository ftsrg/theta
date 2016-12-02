package hu.bme.mit.theta.common.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;

public class BasicScopedSymbol implements ScopedSymbol {

	private final String name;
	private final Scope2 scope;

	public BasicScopedSymbol(final String name, final Scope2 eclosingScope) {
		checkNotNull(name);
		checkArgument(name.length() > 0);
		this.name = name;
		scope = new BasicScope2(eclosingScope);
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public Optional<Symbol> resolve(final String name) {
		return scope.resolve(name);
	}

	@Override
	public void declare(final Symbol symbol) {
		scope.declare(symbol);
	}

	@Override
	public void declareAll(final Collection<? extends Symbol> symbols) {
		scope.declareAll(symbols);
	}

	@Override
	public Optional<Scope2> enclosingScope() {
		return scope.enclosingScope();
	}

}
