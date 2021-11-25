package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.*;

public class SimpleLbePass extends ProcedurePass {

	private final boolean ENABLE_PARALLEL_EDGE_COLLAPSING = true;
	private final boolean ENABLE_SEQUENCE_COLLAPSING = true;

	XcfaProcedure.Builder builder;

	// TODO
	//  * CNF or DNF
	//  * switches for Nondet and Sequences

	/**
	 * Steps of graph transformation:
	 * <p>
	 * 1. Remove outgoing edges of the error location
	 * 2. Join parallel edges to a single edge.
	 * 3. Collapse "snakes" (graph components with vertices that have degrees of one or two).
	 * 4. Obliterate middle-men and join possibly created parallel edges and collapse possibly created snakes.
	 */

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		//if(true) return builder;
		// Print Procedure in DOT format
		String s = builder.toDot(Set.of(), Set.of());
		System.out.println("--- BEFORE TRANSFORMATION ---");
		System.out.println(s);

		this.builder = builder;
		builder = EliminateSelfLoops.instance.run(builder);

		// 1. (this may not be necessary)
		builder.getErrorLoc().getOutgoingEdges().forEach(builder::removeEdge);

		// 2-3.
		joinParallelsAndRemoveSnakes(new ArrayList<>(builder.getLocs()));

		// 4.
		removeMiddleMen();

		s = builder.toDot(Set.of(), Set.of());
		System.out.println("--- DURING TRANSFORMATION ---");
		System.out.println(s);

		for(XcfaLocation location : builder.getLocs()){
			collapseParallelEdges(location, new ArrayList<>());
		}

		// Print Procedure in DOT format
		s = builder.toDot(Set.of(), Set.of());
		System.out.println("--- AFTER TRANSFORMATION ---");
		System.out.println(s);

		return builder;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}

	private List<XcfaLocation> joinParallelsAndRemoveSnakes(List<XcfaLocation> locationsToVisit) {
		List<XcfaLocation> removedLocations = new LinkedList<>();
		while (!locationsToVisit.isEmpty()) {
			XcfaLocation visiting = locationsToVisit.get(0);

			// Join parallel edges starting from "visiting" location
			//collapseParallelEdges(visiting, locationsToVisit);

			// Collapse "visiting" location if it is part of a snake
			collapsePartOfSnake(visiting, locationsToVisit, removedLocations);

			locationsToVisit.remove(visiting);
		}
		return removedLocations;
	}

	private void removeMiddleMen() {
		if (!ENABLE_SEQUENCE_COLLAPSING) return;

		List<XcfaLocation> locationsToVisit = new ArrayList<>(builder.getLocs());
		while (!locationsToVisit.isEmpty()) {
			XcfaLocation visiting = locationsToVisit.get(0);

			if (visiting.getIncomingEdges().size() == 1 && visiting.getOutgoingEdges().size() > 1) {
				XcfaLocation previousLocation = visiting.getIncomingEdges().get(0).getSource();
				removeMiddleLocation(visiting);

				List<XcfaLocation> start = new ArrayList<>();
				start.add(previousLocation);
				List<XcfaLocation> locationsToRemove = joinParallelsAndRemoveSnakes(start);
				locationsToRemove.forEach(locationsToVisit::remove);
			}

			locationsToVisit.remove(visiting);
		}
	}

	private void collapseParallelEdges(XcfaLocation location, List<XcfaLocation> locationsToVisit) {
		if (!ENABLE_PARALLEL_EDGE_COLLAPSING) return;

		HashMap<XcfaLocation, List<XcfaEdge>> edgesByTarget = new HashMap<>();
		for (XcfaEdge edge : location.getOutgoingEdges()) {
			List<XcfaEdge> edgesToTarget = edgesByTarget.getOrDefault(edge.getTarget(), new ArrayList<>());
			edgesToTarget.add(edge);
			edgesByTarget.put(edge.getTarget(), edgesToTarget);
		}
		for (XcfaLocation key : edgesByTarget.keySet()) {
			List<XcfaEdge> edgesToTarget = edgesByTarget.get(key);
			XcfaEdge firstEdge = edgesToTarget.get(0);
			for (XcfaEdge edge : edgesToTarget) {
				if (edge != firstEdge) {
					joinParallelEdges(firstEdge, edge);
				}
			}
			if (edgesToTarget.size() >= 2 && !locationsToVisit.contains(key)) {
				locationsToVisit.add(key);
			}
		}
	}

	private void collapsePartOfSnake(XcfaLocation location, List<XcfaLocation> locationsToVisit, List<XcfaLocation> removedLocations) {
		if (!ENABLE_SEQUENCE_COLLAPSING) return;

		if (location.getIncomingEdges().size() == 1 && location.getOutgoingEdges().size() == 1) {
			XcfaLocation previousLocation = location.getIncomingEdges().get(0).getSource();
			removeMiddleLocation(location);
			removedLocations.add(location);
			if (!locationsToVisit.contains(previousLocation)) {
				locationsToVisit.add(previousLocation);
			}
		}
	}

	private XcfaLabel getWrappedLabels(XcfaEdge edge) {
		List<XcfaLabel> edgeLabels = edge.getLabels();
		return edgeLabels.size() == 1 ? edgeLabels.get(0) : XcfaLabel.Sequence(edgeLabels);
	}

	private void joinParallelEdges(XcfaEdge edge1, XcfaEdge edge2) {
		if (edge1.getSource() != edge2.getSource() || edge1.getTarget() != edge2.getTarget()) return;
		builder.removeEdge(edge1);
		builder.removeEdge(edge2);
		XcfaLabel jointLabel = XcfaLabel.Nondet(List.of(
				getWrappedLabels(edge1),
				getWrappedLabels(edge2)
		));
		builder.addEdge(XcfaEdge.of(edge1.getSource(), edge2.getTarget(), List.of(jointLabel)));
	}

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