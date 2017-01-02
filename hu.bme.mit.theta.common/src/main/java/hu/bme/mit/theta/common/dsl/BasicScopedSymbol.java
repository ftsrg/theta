package hu.bme.mit.theta.common.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;

public final class BasicScopedSymbol implements ScopedSymbol {

	private final String name;
	private final BasicScope scope;

	public BasicScopedSymbol(final String name, final Scope eclosingScope, final Collection<? extends Symbol> symbols) {
		checkNotNull(name);
		checkArgument(name.length() > 0);
		this.name = name;
		scope = new BasicScope(eclosingScope);
	}

	////

	public void declare(final Symbol symbol) {
		scope.declare(symbol);
	}

	public void declareAll(final Collection<? extends Symbol> symbols) {
		scope.declareAll(symbols);
	}

	////

	@Override
	public String getName() {
		return name;
	}

	@Override
	public Optional<? extends Symbol> resolve(final String name) {
		return scope.resolve(name);
	}

	@Override
	public Optional<? extends Scope> enclosingScope() {
		return scope.enclosingScope();
	}

}
