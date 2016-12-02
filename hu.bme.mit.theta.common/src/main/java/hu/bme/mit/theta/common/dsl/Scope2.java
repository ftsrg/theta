package hu.bme.mit.theta.common.dsl;

import java.util.Collection;
import java.util.Optional;

public interface Scope2 extends Scope {

	void declare(Symbol symbol);

	default void declareAll(final Collection<? extends Symbol> symbols) {
		symbols.stream().forEach(this::declare);
	}

	@Override
	Optional<Scope2> enclosingScope();

	@Override
	Optional<Symbol> resolve(String name);

}
