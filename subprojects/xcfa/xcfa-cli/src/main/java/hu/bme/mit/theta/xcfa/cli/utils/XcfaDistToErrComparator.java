/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.cli.utils;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.ArgNodeComparator;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import kotlin.Pair;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

/**
 * A comparator for ArgNodes that is based on the distance from the error
 * location.
 */
public class XcfaDistToErrComparator implements ArgNodeComparator {
    private Map<XcfaLocation, Integer> distancesToError;
    private final int errorWeight;
    private final int depthWeight;
    private final XCFA xcfa;
    private final XcfaLocation errLoc;

    public XcfaDistToErrComparator(final XCFA xcfa) {
        this(xcfa, 1, 0);
    }

    public XcfaDistToErrComparator(final XCFA xcfa, final int errorWeight, final int depthWeight) {
        this.xcfa = xcfa;
        Pair<XcfaProcedure, List<Expr<?>>> initProc = checkNotNull(xcfa.getInitProcedures().get(0));
        Optional<XcfaLocation> errorLocOpt = initProc.component1().getErrorLoc();
//        checkState(errorLocOpt.isPresent());
        this.errLoc = errorLocOpt.orElse(null);
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
        final var localState = node.getState();
        checkArgument(localState instanceof XcfaState && ((XcfaState) localState).getProcesses().size() <= 1, "XcfaState expected with a single process.");
        if (((XcfaState) localState).getProcesses().size() == 0) {
            return Integer.MAX_VALUE;
        }
        final XcfaState<?> state = (XcfaState<?>) localState;
        final int distanceToError = getDistanceToError(state.getProcesses().get(0).component1().peek());
        if (distanceToError == Integer.MAX_VALUE) {
            return distanceToError;
        }
        return errorWeight * distanceToError + depthWeight * node.getDepth();
    }

    private int getDistanceToError(final XcfaLocation loc) {
        if (distancesToError == null && errLoc != null) {
            distancesToError = calculateDistancesToError(xcfa, errLoc);
        } else if (errLoc == null) {
            return Integer.MAX_VALUE;
        }
        return distancesToError.getOrDefault(loc, Integer.MAX_VALUE);
    }

    static Map<XcfaLocation, Integer> calculateDistancesToError(final XCFA cfa, final XcfaLocation errLoc) {
        List<XcfaLocation> queue = new LinkedList<>();
        final Map<XcfaLocation, Integer> distancesToError = Containers.createMap();
        queue.add(errLoc);
        distancesToError.put(errLoc, 0);
        int distance = 1;

        while (!queue.isEmpty()) {
            final List<XcfaLocation> predecessors = new LinkedList<>();
            for (final XcfaLocation loc : queue) {
                for (final XcfaEdge inEdge : loc.getIncomingEdges()) {
                    final XcfaLocation predecessor = inEdge.getSource();
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
