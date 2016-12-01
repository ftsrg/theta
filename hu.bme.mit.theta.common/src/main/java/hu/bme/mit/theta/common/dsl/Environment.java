package hu.bme.mit.theta.common.dsl;

import java.util.List;
import java.util.Optional;

public interface Environment {

	Optional<Object> valuation(Symbol symbol);

	void define(Symbol symbol, Object value);

	void defineAll(List<? extends Symbol> symbols, List<? extends Object> values);

	Optional<Environment> enclosingEnvironment();

}
