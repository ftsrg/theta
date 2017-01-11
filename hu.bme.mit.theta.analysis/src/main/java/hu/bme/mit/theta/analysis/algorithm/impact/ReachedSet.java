package hu.bme.mit.theta.analysis.algorithm.impact;

import java.util.stream.Stream;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;

public interface ReachedSet<S extends State, A extends Action> {

	void add(ArgNode<S, A> node);

	default void addAll(final Iterable<? extends ArgNode<S, A>> nodes) {
		nodes.forEach(this::add);
	}

	default void addAll(final Stream<? extends ArgNode<S, A>> nodes) {
		nodes.forEach(this::add);
	}

	void tryToCover(ArgNode<S, A> node);

}
