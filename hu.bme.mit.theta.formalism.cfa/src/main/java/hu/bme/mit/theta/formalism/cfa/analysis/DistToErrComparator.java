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

public class DistToErrComparator implements ArgNodeComparator {
	private static final long serialVersionUID = -6915823336852930450L;

	private final Map<Loc, Integer> distancesToError;

	public DistToErrComparator(final CFA cfa) {
		distancesToError = getDistancesToError(cfa);
	}

	@Override
	public int compare(final ArgNode<? extends State, ? extends Action> n1,
			final ArgNode<? extends State, ? extends Action> n2) {
		checkArgument(n1.getState() instanceof CfaState, "CfaState expected.");
		checkArgument(n2.getState() instanceof CfaState, "CfaState expected.");
		final CfaState<?> s1 = (CfaState<?>) n1.getState();
		final CfaState<?> s2 = (CfaState<?>) n2.getState();

		final int dist1 = distancesToError.getOrDefault(s1.getLoc(), Integer.MAX_VALUE);
		final int dist2 = distancesToError.getOrDefault(s2.getLoc(), Integer.MAX_VALUE);

		return Integer.compare(dist1, dist2);
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

}
