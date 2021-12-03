package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.*;

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
public class SimpleLbePass extends ProcedurePass {
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

	XcfaProcedure.Builder builder;

	/**
	 * Steps of graph transformation:
	 *
	 * <ol>
	 *     	<li>Remove outgoing edges of the error location</li>
	 * 		<li>Join parallel edges to single edges and collapse snakes (see Definitions at {@link SimpleLbePass})</li>
	 * 	 	<li>Collapse sequential edges of locations whose incoming degree is 1, join possibly created parallel edges and
	 * 	 	edge-pairs described in step 2</li>
	 * </ol>
	 */
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		if (level == LBELevel.NO_LBE) return builder;

		if (ENABLE_PRINT_TO_DOT) {
			System.out.println("--- BEFORE TRANSFORMATION ---");
			System.out.println(builder.toDot(Set.of(), Set.of()));
		}

		this.builder = builder;
		builder = EliminateSelfLoops.instance.run(builder);

		// Step 1
		builder.getErrorLoc().getOutgoingEdges().forEach(builder::removeEdge);

		// Step 2
		collapseParallelsAndSnakes(new ArrayList<>(builder.getLocs()));

		// Step 3
		removeAllMiddleLocations();

		//builder = EliminateSelfLoops.instance.run(builder);

		if (ENABLE_PRINT_TO_DOT) {
			System.out.println("--- AFTER TRANSFORMATION ---");
			System.out.println(builder.toDot(Set.of(), Set.of()));
		}

		return builder;
	}

	@Override
	public boolean isPostInlining() {
		return true;
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
				XcfaLocation previousLocation = visiting.getIncomingEdges().get(0).getSource();
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
			XcfaLabel.NondetLabel nondetLabel = XcfaLabel.Nondet(new ArrayList<>());
			for (XcfaEdge edge : edgesToTarget) {
				List<XcfaLabel> oldLabels = new ArrayList<>(nondetLabel.getLabels());
				oldLabels.addAll(getNonDetBranch(edge.getLabels()));
				nondetLabel = XcfaLabel.Nondet(oldLabels);
				builder.removeEdge(edge);
			}
			builder.addEdge(XcfaEdge.of(source, target, List.of(nondetLabel)));

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
			XcfaLocation previousLocation = location.getIncomingEdges().get(0).getSource();
			removeMiddleLocation(location);
			removedLocations.add(location);
			if (!locationsToVisit.contains(previousLocation)) {
				locationsToVisit.add(previousLocation);
			}
		}
	}

	/**
	 * Wraps edge labels to a {@link hu.bme.mit.theta.xcfa.model.XcfaLabel.SequenceLabel} if the edge does not have
	 * exactly
	 * one label. If the labels contain one {@link hu.bme.mit.theta.xcfa.model.XcfaLabel.NondetLabel}, the NondetLabel's
	 * labels are returned
	 * in a list to achieve DNF.
	 *
	 * @param edgeLabels the edge labels we would like to add to the NonDetLabel
	 * @return the list of labels to add to the NonDetLabel
	 */
	private List<XcfaLabel> getNonDetBranch(List<XcfaLabel> edgeLabels) {
		if (edgeLabels.size() == 1) {
			if (edgeLabels.get(0) instanceof XcfaLabel.NondetLabel) {
				return ((XcfaLabel.NondetLabel) edgeLabels.get(0)).getLabels();
			}
			return edgeLabels;
		}
		List<XcfaLabel> labels = new ArrayList<>();
		labels.add(XcfaLabel.Sequence(edgeLabels));
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
		XcfaEdge inEdge = location.getIncomingEdges().get(0);
		builder.removeEdge(inEdge);
		builder.removeLoc(location);

		List<XcfaEdge> edgesToRemove = List.copyOf(location.getOutgoingEdges());
		for (XcfaEdge outEdge : edgesToRemove) {
			builder.removeEdge(outEdge);
			List<XcfaLabel> stmts = new ArrayList<>(inEdge.getLabels());
			stmts.addAll(outEdge.getLabels());
			builder.addEdge(XcfaEdge.of(inEdge.getSource(), outEdge.getTarget(), stmts));
		}
	}
}