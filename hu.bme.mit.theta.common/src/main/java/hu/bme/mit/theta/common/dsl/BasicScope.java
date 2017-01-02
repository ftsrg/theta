package hu.bme.mit.theta.common.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;

public final class BasicScope implements Scope {

	private final Optional<Scope> enclosingScope;
	private final SymbolTable symbolTable;

	public BasicScope(final Scope eclosingScope) {
		this.enclosingScope = Optional.ofNullable(eclosingScope);
		symbolTable = new SymbolTable();
	}

	////

	public void declare(final Symbol symbol) {
		symbolTable.add(symbol);
	}

	public void declareAll(final Collection<? extends Symbol> symbols) {
		symbolTable.addAll(symbols);
	}

	////

	@Override
	public Optional<Scope> enclosingScope() {
		return enclosingScope;
	}

	@Override
	public Optional<? extends Symbol> resolve(final String name) {
		checkNotNull(name);
		final Optional<Symbol> symbol = symbolTable.get(name);
		if (symbol.isPresent() || !enclosingScope.isPresent()) {
			return symbol;
		} else {
			return enclosingScope.get().resolve(name);
		}
	}

}
