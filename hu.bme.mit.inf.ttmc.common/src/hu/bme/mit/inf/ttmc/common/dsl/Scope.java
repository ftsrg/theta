package hu.bme.mit.inf.ttmc.common.dsl;

import java.util.Collection;
import java.util.Optional;

public interface Scope {

	public Optional<Symbol> resolve(String name);

	public void declare(Symbol symbol);

	public void declareAll(Collection<? extends Symbol> symbols);

	public Optional<Scope> enclosingScope();

}
