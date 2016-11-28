package hu.bme.mit.theta.common.dsl;

import java.util.Collection;
import java.util.Optional;

public interface Scope {

	Optional<Symbol> resolve(String name);

	void declare(Symbol symbol);

	void declareAll(Collection<? extends Symbol> symbols);

	Optional<Scope> enclosingScope();

}
