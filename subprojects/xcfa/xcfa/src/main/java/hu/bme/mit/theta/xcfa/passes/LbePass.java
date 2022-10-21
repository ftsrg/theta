/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.passes;

import hu.bme.mit.theta.xcfa.model.*;

import java.util.*;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

/**
 * This pass simplifies the XCFA by joining certain edges to single edges.
 * <p>
 * Definitions:
 * <ul>
 *     <li>Parallel edges: edges with the same source and target location</li>
 *     <li>Snake: a graph component where the incoming and outgoing degree of every location is 1 (except at the ends)</li>
 *     <li>Middle location: a location whose incoming degree is 1</li>
 * </ul>
 */
public class LbePass implements ProcedurePass {
	/**
	 * The level of LBE that specifies which type of graph transformations to apply.
	 */
	public static LBELevel level = LBELevel.NO_LBE;

	/**
	 * LBE modes.
	 */
	public enum LBELevel {
		/**
		 * The pass returns the builder without applying any changes.
		 */
		NO_LBE,

		/**
		 * Enables collapsing of sequential edges of a location where the number of incoming edges to the location is
		 * exactly 1. A new edge is created for every outgoing edge of the location combined with the labels of the
		 * incoming
		 * edge. Parallel edges are not collapsed.
		 */
		LBE_SEQ,

		/**
		 * Enables collapsing of sequential and parallel edges too.
		 */
		LBE_FULL
	}

	/**
	 * Enables printing of the XCFA before and after the transformation process. For debugging...
	 */
	private final boolean ENABLE_PRINT_TO_DOT = false;

	XcfaProcedureBuilder builder;

	/**
	 * Steps of graph transformation:
	 *
	 * <ol>
	 *     	<li>Remove outgoing edges of the error location</li>
	 * 		<li>Join parallel edges to single edges and collapse snakes (see Definitions at {@link LbePass})</li>
	 * 	 	<li>Collapse sequential edges of locations whose incoming degree is 1, join possibly created parallel edges and
	 * 	 	edge-pairs described in step 2</li>
	 * </ol>
	 */
	@Override
	public XcfaProcedureBuilder run(XcfaProcedureBuilder builder) {
		if (level == LBELevel.NO_LBE) return builder;
		checkNotNull(builder.getMetaData().get("deterministic"));
		checkNotNull(builder.getMetaData().get("noSelfLoops"));

		this.builder = builder;

		printToDot("--- BEFORE TRANSFORMATION ---");

		// Step 1
		checkState(builder.getErrorLoc().isPresent());
		builder.getErrorLoc().get().getOutgoingEdges().forEach(builder::removeEdge);

		// Step 2
		collapseParallelsAndSnakes(new ArrayList<>(builder.getLocs()));

		// Step 3
		removeAllMiddleLocations();

		printToDot("--- AFTER TRANSFORMATION ---");

		return builder;
	}

	/**
	 * Collapses parallel edges and snakes with a starting list of locations to check. Possibly created new parallel
	 * edges and snakes are collapsed too.
	 *
	 * @param locationsToVisit The starting list of locations to check.
	 * @return Returns the list of removed locations.
	 */
	private List<XcfaLocation> collapseParallelsAndSnakes(List<XcfaLocation> locationsToVisit) {
		List<XcfaLocation> removedLocations = new LinkedList<>();
		while (!locationsToVisit.isEmpty()) {
			XcfaLocation visiting = locationsToVisit.get(0);

			// Join parallel edges starting from "visiting" location
			if (level == LBELevel.LBE_FULL) {
				collapseParallelEdges(visiting, locationsToVisit);
			}

			// Collapse "visiting" location if it is part of a snake
			collapsePartOfSnake(visiting, locationsToVisit, removedLocations);

			locationsToVisit.remove(visiting);
		}
		return removedLocations;
	}

	/**
	 * Removes locations whose incoming degree is 1. A new edge is created for every outgoing edge of the location
	 * combined with the labels of the incoming edge as a sequence (the labels of the incoming edge will be the first in
	 * the sequence).
	 */
	private void removeAllMiddleLocations() {
		List<XcfaLocation> locationsToVisit = new ArrayList<>(builder.getLocs());
		while (!locationsToVisit.isEmpty()) {
			XcfaLocation visiting = locationsToVisit.get(0);

			if (visiting.getIncomingEdges().size() == 1 && visiting.getOutgoingEdges().size() > 1) {
				XcfaLocation previousLocation = visiting.getIncomingEdges().stream().findAny().get().getSource();
				removeMiddleLocation(visiting);

				List<XcfaLocation> start = new ArrayList<>();
				start.add(previousLocation);
				List<XcfaLocation> locationsToRemove = collapseParallelsAndSnakes(start);
				locationsToRemove.forEach(locationsToVisit::remove);
			}

			locationsToVisit.remove(visiting);
		}
	}

	/**
	 * Collapses all parallel edges starting from a location.
	 *
	 * @param location         the location from where the parallel edges start that we want to remove
	 * @param locationsToVisit Adds the targets of parallel edges to this list (new parallel edges and snakes
	 *                         can appear in these locations)
	 */
	private void collapseParallelEdges(XcfaLocation location, List<XcfaLocation> locationsToVisit) {
		HashMap<XcfaLocation, List<XcfaEdge>> edgesByTarget = new HashMap<>();
		for (XcfaEdge edge : location.getOutgoingEdges()) {
			List<XcfaEdge> edgesToTarget = edgesByTarget.getOrDefault(edge.getTarget(), new ArrayList<>());
			edgesToTarget.add(edge);
			edgesByTarget.put(edge.getTarget(), edgesToTarget);
		}
		for (XcfaLocation key : edgesByTarget.keySet()) {
			List<XcfaEdge> edgesToTarget = edgesByTarget.get(key);
			if (edgesToTarget.size() <= 1) continue;
			XcfaLocation source = edgesToTarget.get(0).getSource();
			XcfaLocation target = edgesToTarget.get(0).getTarget();
			NondetLabel nondetLabel = new NondetLabel(new LinkedHashSet<>());
			for (XcfaEdge edge : edgesToTarget) {
				Set<XcfaLabel> oldLabels = new LinkedHashSet<>(nondetLabel.getLabels());
				oldLabels.addAll(getNonDetBranch(List.of(edge.getLabel())));
				nondetLabel = new NondetLabel(oldLabels);
				builder.removeEdge(edge);
			}
			builder.addEdge(new XcfaEdge(source, target, nondetLabel));

			if (edgesToTarget.size() >= 2 && !locationsToVisit.contains(key)) {
				locationsToVisit.add(key);
			}
		}
	}

	/**
	 * Collapses the incoming and outgoing edges of a location whose incoming and outgoing degree is 1.
	 *
	 * @param location         The location to collapse
	 * @param locationsToVisit The change list, the location that is the source of the incoming edge of the location is
	 *                         added to this list
	 * @param removedLocations The list of removed locations: the collapsed location is added to this list
	 */
	private void collapsePartOfSnake(XcfaLocation location, List<XcfaLocation> locationsToVisit, List<XcfaLocation> removedLocations) {
		if (location.getIncomingEdges().size() == 1 && location.getOutgoingEdges().size() == 1) {
			XcfaLocation previousLocation = location.getIncomingEdges().stream().findAny().get().getSource();
			removeMiddleLocation(location);
			removedLocations.add(location);
			if (!locationsToVisit.contains(previousLocation)) {
				locationsToVisit.add(previousLocation);
			}
		}
	}

	/**
	 * Wraps edge labels to a {@link SequenceLabel} if the edge does not have
	 * exactly one label. If the labels contain one {@link NondetLabel}, the NondetLabel's
	 * labels are returned to simplify the formula.
	 *
	 * @param edgeLabels the edge labels we would like to add to the NonDetLabel
	 * @return the list of labels to add to the NonDetLabel
	 */
	private Collection<XcfaLabel> getNonDetBranch(List<XcfaLabel> edgeLabels) {
		if (edgeLabels.size() == 1) {
			XcfaLabel first = edgeLabels.stream().findAny().get();
			if (first instanceof NondetLabel) {
				return ((NondetLabel) first).getLabels();
			}
			return edgeLabels;
		}
		Set<XcfaLabel> labels = new LinkedHashSet<>();
		labels.add(new SequenceLabel(edgeLabels));
		return labels;
	}

	/**
	 * Removes a location whose incoming degree is 1. A new edge is created for every outgoing edge of the location
	 * combined with the labels of the incoming edge as a sequence (the labels of the incoming edge will be the first in
	 * the sequence).
	 *
	 * @param location The location to remove
	 */
	private void removeMiddleLocation(XcfaLocation location) {
		if (location.getIncomingEdges().size() != 1) return;
		XcfaEdge inEdge = location.getIncomingEdges().stream().findAny().get();
		builder.removeEdge(inEdge);
		builder.removeLoc(location);

		List<XcfaEdge> edgesToRemove = List.copyOf(location.getOutgoingEdges());
		for (XcfaEdge outEdge : edgesToRemove) {
			builder.removeEdge(outEdge);
			List<XcfaLabel> newLabel = new ArrayList<>();

			newLabel.add(inEdge.getLabel());
			newLabel.add(outEdge.getLabel());

			builder.addEdge(new XcfaEdge(inEdge.getSource(), outEdge.getTarget(), new SequenceLabel(newLabel)));
		}
	}

	/**
	 * Prints the XCFA in dot format to standard output.
	 *
	 * @param title the printed XCFA will be marked with this label
	 */
	private void printToDot(String title) {
		if (ENABLE_PRINT_TO_DOT) {
			System.out.println(title);
			System.out.println("digraph G {");
//			System.out.println(builder.toDot(Set.of(), Set.of()));
			System.out.println("}");
		}
	}
}