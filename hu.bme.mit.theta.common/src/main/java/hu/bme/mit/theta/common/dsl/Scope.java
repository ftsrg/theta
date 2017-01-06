package hu.bme.mit.theta.common.dsl;

import java.util.Optional;

public interface Scope {

	Optional<? extends Scope> enclosingScope();

	Optional<? extends Symbol> resolve(String name);

}
