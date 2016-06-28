package hu.bme.mit.inf.ttmc.analysis;

import java.util.function.Predicate;

@FunctionalInterface
public interface StatePredicate<S extends State> extends Predicate<S> {

}
