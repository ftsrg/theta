package hu.bme.mit.theta.common.dsl;

import java.util.Collection;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkNotNull;

public class BasicDynamicScope implements DynamicScope  {
	private final Optional<DynamicScope> enclosingScope;
	private final SymbolTable symbolTable;

	public BasicDynamicScope(final DynamicScope enclosingScope) {
		this.enclosingScope = Optional.ofNullable(enclosingScope);
		symbolTable = new SymbolTable();
	}

	////

	@Override
	public void declare(final Symbol symbol) {
		symbolTable.add(symbol);
	}

	@Override
	public void declareAll(final Collection<? extends Symbol> symbols) {
		symbolTable.addAll(symbols);
	}

	////

	@Override
	public Optional<DynamicScope> enclosingScope() {
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
