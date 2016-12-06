package hu.bme.mit.theta.common.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;

public final class BasicScope2 implements Scope2 {

	private final Optional<Scope2> enclosingScope;

	private final SymbolTable symbolTable;

	public BasicScope2(final Scope2 eclosingScope) {
		this.enclosingScope = Optional.ofNullable(eclosingScope);
		symbolTable = new SymbolTable();
	}

	@Override
	public Optional<Scope2> enclosingScope() {
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
