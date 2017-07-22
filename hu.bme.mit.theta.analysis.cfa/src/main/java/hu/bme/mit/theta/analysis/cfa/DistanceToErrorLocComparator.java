package hu.bme.mit.theta.analysis.cfa;

import java.io.Serializable;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaLoc;

public class DistanceToErrorLocComparator implements
		Comparator<ArgNode<? extends LocState<? extends State, CfaLoc, CfaEdge>, ? extends Action>>, Serializable {
	private static final long serialVersionUID = -6915823336852930450L;

	private final Map<CfaLoc, Integer> distancesToError;

	public DistanceToErrorLocComparator(final CFA cfa) {
		distancesToError = getDistancesToError(cfa);
	}

	@Override
	public int compare(final ArgNode<? extends LocState<? extends State, CfaLoc, CfaEdge>, ? extends Action> n1,
			final ArgNode<? extends LocState<? extends State, CfaLoc, CfaEdge>, ? extends Action> n2) {
		final int dist1 = distancesToError.getOrDefault(n1.getState().getLoc(), Integer.MAX_VALUE);
		final int dist2 = distancesToError.getOrDefault(n2.getState().getLoc(), Integer.MAX_VALUE);

		return Integer.compare(dist1, dist2) * -1;
	}

	static Map<CfaLoc, Integer> getDistancesToError(final CFA cfa) {
		List<CfaLoc> queue = new LinkedList<>();
		final Map<CfaLoc, Integer> distancesToError = new HashMap<>();
		queue.add(cfa.getErrorLoc());
		distancesToError.put(cfa.getErrorLoc(), 0);
		int distance = 1;

		while (!queue.isEmpty()) {
			final List<CfaLoc> predecessors = new LinkedList<>();
			for (final CfaLoc loc : queue) {
				for (final CfaEdge inEdge : loc.getInEdges()) {
					final CfaLoc predecessor = inEdge.getSource();
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
