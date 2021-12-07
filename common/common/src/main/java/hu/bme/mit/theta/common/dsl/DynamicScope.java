package hu.bme.mit.theta.common.dsl;

import java.util.Collection;
import java.util.Optional;

public interface DynamicScope extends Scope{

	void declare(final Symbol symbol);

	void declareAll(final Collection<? extends Symbol> symbols);

	Optional<? extends DynamicScope> enclosingScope();

}
