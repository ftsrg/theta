package hu.bme.mit.theta.common.dsl;

import java.util.List;
import java.util.Optional;

public interface Environment {

	public Optional<Object> valuation(Symbol symbol);

	public void define(Symbol symbol, Object value);

	public void defineAll(List<? extends Symbol> symbols, List<? extends Object> values);

	public Optional<Environment> enclosingEnvironment();

}
