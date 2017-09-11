package hu.bme.mit.theta.formalism.cfa.analysis;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.ArgNodeComparator;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.Edge;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

/**
 * A comparator for ArgNodes that is based on the distance from the error
 * location.
 */
public class DistToErrComparator implements ArgNodeComparator {
	private static final long serialVersionUID = -6915823336852930450L;

	private Map<Loc, Integer> distancesToError;
	private final CFA cfa;

	public DistToErrComparator(final CFA cfa) {
		this.cfa = cfa;
		distancesToError = null;
	}

	@Override
	public int compare(final ArgNode<? extends State, ? extends Action> n1,
			final ArgNode<? extends State, ? extends Action> n2) {
		checkArgument(n1.getState() instanceof CfaState, "CfaState expected.");
		checkArgument(n2.getState() instanceof CfaState, "CfaState expected.");

		final CfaState<?> s1 = (CfaState<?>) n1.getState();
		final CfaState<?> s2 = (CfaState<?>) n2.getState();

		final int dist1 = getDistance(s1.getLoc());
		final int dist2 = getDistance(s2.getLoc());

		return Integer.compare(dist1, dist2);
	}

	private int getDistance(final Loc loc) {
		if (distancesToError == null) {
			distancesToError = getDistancesToError(cfa);
		}
		return distancesToError.getOrDefault(loc, Integer.MAX_VALUE);
	}

	static Map<Loc, Integer> getDistancesToError(final CFA cfa) {
		List<Loc> queue = new LinkedList<>();
		final Map<Loc, Integer> distancesToError = new HashMap<>();
		queue.add(cfa.getErrorLoc());
		distancesToError.put(cfa.getErrorLoc(), 0);
		int distance = 1;

		while (!queue.isEmpty()) {
			final List<Loc> predecessors = new LinkedList<>();
			for (final Loc loc : queue) {
				for (final Edge inEdge : loc.getInEdges()) {
					final Loc predecessor = inEdge.getSource();
					if (!distancesToError.containsKey(predecessor)) {
						distancesToError.put(predecessor, distance);
						predecessors.add(predecessor);
					}
				}
			}
			queue = predecessors;
			++distance;
		}

		return distancesToError;
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
