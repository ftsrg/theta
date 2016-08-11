package hu.bme.mit.inf.ttmc.common.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;

public abstract class BasicScope implements Scope {

	final Optional<Scope> enclosingScope;

	final SymbolTable symbolTable;

	public BasicScope(final Scope eclosingScope) {
		this.enclosingScope = Optional.ofNullable(eclosingScope);
		symbolTable = new SymbolTable();
	}

	@Override
	public Optional<Scope> enclosingScope() {
		return enclosingScope;
	}

	@Override
	public Optional<Symbol> resolve(final String name) {
		checkNotNull(name);
		final Optional<Symbol> symbol = symbolTable.get(name);
		if (symbol.isPresent() || !enclosingScope.isPresent()) {
			return symbol;
		} else {
			return enclosingScope.get().resolve(name);
		}
	}

	@Override
	public void declare(final Symbol symbol) {
		symbolTable.add(symbol);
	}

}
