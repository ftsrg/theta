package hu.bme.mit.theta.analysis.algorithm.impact;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;

public abstract class AbstractReachedSet<S extends State, A extends Action> implements ReachedSet<S, A> {

	protected abstract Collection<? extends ArgNode<S, A>> getCandidatesForCovering(ArgNode<S, A> node);

	@Override
	public final void tryToCover(final ArgNode<S, A> node) {
		if (!node.isExcluded()) {
			for (final ArgNode<S, A> candidate : getCandidatesForCovering(node)) {
				if (candidate.mayCover(node)) {
					node.cover(candidate);
				}
			}
		}
	}

}
