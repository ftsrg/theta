/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.cfa.analysis;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.ArgNodeComparator;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.CFA.Edge;
import hu.bme.mit.theta.cfa.CFA.Loc;

/**
 * A comparator for ArgNodes that is based on the distance from the error
 * location.
 */
public class DistToErrComparator implements ArgNodeComparator {
	private static final long serialVersionUID = -6915823336852930450L;

	private Map<Loc, Integer> distancesToError;
	private final int errorWeight;
	private final int depthWeight;
	private final CFA cfa;
	private final Loc errLoc;

	public DistToErrComparator(final CFA cfa, final Loc errLoc) {
		this(cfa, errLoc, 1, 0);
	}

	public DistToErrComparator(final CFA cfa, final Loc errLoc, final int errorWeight, final int depthWeight) {
		this.cfa = cfa;
		this.errLoc = errLoc;
		this.errorWeight = errorWeight;
		this.depthWeight = depthWeight;
		distancesToError = null;
	}

	@Override
	public int compare(final ArgNode<? extends State, ? extends Action> n1,
					   final ArgNode<? extends State, ? extends Action> n2) {
		final int dist1 = getWeightedDistance(n1);
		final int dist2 = getWeightedDistance(n2);

		return Integer.compare(dist1, dist2);
	}

	private int getWeightedDistance(final ArgNode<? extends State, ? extends Action> node) {
		checkArgument(node.getState() instanceof CfaState, "CfaState expected.");
		final CfaState<?> state = (CfaState<?>) node.getState();
		final int distanceToError = getDistanceToError(state.getLoc());
		if (distanceToError == Integer.MAX_VALUE) {
			return distanceToError;
		}
		return errorWeight * distanceToError + depthWeight * node.getDepth();
	}

	private int getDistanceToError(final Loc loc) {
		if (distancesToError == null) {
			distancesToError = calculateDistancesToError(cfa, errLoc);
		}
		return distancesToError.getOrDefault(loc, Integer.MAX_VALUE);
	}

	static Map<Loc, Integer> calculateDistancesToError(final CFA cfa, final Loc errLoc) {
		List<Loc> queue = new LinkedList<>();
		final Map<Loc, Integer> distancesToError = new HashMap<>();
		queue.add(errLoc);
		distancesToError.put(errLoc, 0);
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