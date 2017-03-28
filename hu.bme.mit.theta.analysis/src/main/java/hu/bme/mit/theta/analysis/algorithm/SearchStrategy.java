package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.bfs;
import static hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.dfs;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.ArgNodeComparator;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;

public enum SearchStrategy {

	BREADTH_FIRST(bfs()),

	DEPTH_FIRST(dfs());

	private final ArgNodeComparator comparator;

	private SearchStrategy(final ArgNodeComparator comparator) {
		this.comparator = checkNotNull(comparator);
	}

	public <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist() {
		return PriorityWaitlist.create(comparator);
	}

}
