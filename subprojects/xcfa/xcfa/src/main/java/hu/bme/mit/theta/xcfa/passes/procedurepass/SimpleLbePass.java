package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.*;
import java.util.stream.Collectors;

public class SimpleLbePass extends ProcedurePass {

	XcfaProcedure.Builder builder;

	/**
	 * Steps of graph transformation:
	 *
	 * 1. Remove outgoing edges of the error location
	 * 2. Join parallel edges to a single edge.
	 * 3. Collapse "snakes" (graph components with vertices that have degrees of one or two).
	 * 4. Obliterate middle-men and join possibly created parallel edges and collapse possibly created snakes.
	 */

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		// Print Procedure in DOT format
		String s = builder.toDot(Set.of(), Set.of());
		System.out.println(s);

		this.builder = builder;
		builder = EliminateSelfLoops.instance.run(builder);

		// 1. (this may not be necessary)
		builder.getErrorLoc().getOutgoingEdges().forEach(builder::removeEdge);

		// 2-3.
		joinParallelsAndRemoveSnakes(new ArrayList<>(builder.getLocs()));

		// 4.
		List<XcfaLocation> locationsToVisit = new ArrayList<>(builder.getLocs());
		while (!locationsToVisit.isEmpty()) {
			XcfaLocation visiting = locationsToVisit.get(0);

			if (visiting.getIncomingEdges().size() == 1 && visiting.getOutgoingEdges().size() > 1) {
				XcfaLocation previousLocation = visiting.getIncomingEdges().get(0).getSource();
				removeMiddleLocation(visiting);

				List<XcfaLocation> locationsToRemove = joinParallelsAndRemoveSnakes(Arrays.asList(previousLocation));
				locationsToRemove.forEach(locationsToVisit::remove);
			}

			locationsToVisit.remove(visiting);
		}

		/*final List<XcfaEdge> edgesToHandle = builder.getEdges().stream().filter(xcfaEdge -> xcfaEdge.getLabels().stream().anyMatch(label -> !(label instanceof XcfaLabel.StmtXcfaLabel))).collect(Collectors.toList());
		for (XcfaEdge edge : edgesToHandle) {
			builder.removeEdge(edge);
			List<XcfaLabel> newLabelList = new ArrayList<>();
			XcfaLocation source = edge.getSource();
			for (XcfaLabel label : edge.getLabels()) {
				if (!(label instanceof XcfaLabel.StmtXcfaLabel)) {
					if (newLabelList.size() > 0) {
						XcfaLocation tmpLoc = XcfaLocation.create("_tmp" + XcfaLocation.uniqeCounter());
						builder.addLoc(tmpLoc);
						builder.addEdge(XcfaEdge.of(source, tmpLoc, newLabelList));
						source = tmpLoc;
					}
					newLabelList.clear();
					XcfaLocation tmpLoc = XcfaLocation.create("_tmp" + XcfaLocation.uniqeCounter());
					builder.addLoc(tmpLoc);
					builder.addEdge(XcfaEdge.of(source, tmpLoc, List.of(label)));
					source = tmpLoc;
				} else {
					newLabelList.add(label);
				}
			}
			builder.addEdge(XcfaEdge.of(source, edge.getTarget(), newLabelList));
		}*/

		// Print Procedure in DOT format
		s = builder.toDot(Set.of(), Set.of());
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
			HashMap<XcfaLocation, List<XcfaEdge>> edgesByTarget = new HashMap<>();
			for (XcfaEdge edge : visiting.getOutgoingEdges()) {
				List<XcfaEdge> edgesToTarget = edgesByTarget.get(edge.getTarget());
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

			// Collapse "visiting" location if it is part of a snake
			if (visiting.getIncomingEdges().size() == 1 && visiting.getOutgoingEdges().size() == 1) {
				XcfaLocation previousLocation = visiting.getIncomingEdges().get(0).getSource();
				removeMiddleLocation(visiting);
				removedLocations.add(visiting);
				if (!locationsToVisit.contains(previousLocation)) {
					locationsToVisit.add(previousLocation);
				}
			}

			locationsToVisit.remove(visiting);
		}
		return removedLocations;
	}

	private void joinParallelEdges(XcfaEdge edge1, XcfaEdge edge2) {
		// TODO check whether edge1 and edge2 are parallel if necessary
		builder.removeEdge(edge1);
		builder.removeEdge(edge2);
		XcfaLabel jointLabel = XcfaLabel.Nondet(List.of(
				XcfaLabel.Sequence(edge1.getLabels()),
				XcfaLabel.Sequence(edge2.getLabels())
		));
		builder.addEdge(XcfaEdge.of(edge1.getSource(), edge2.getTarget(), List.of(jointLabel)));
	}

	private void removeMiddleLocation(XcfaLocation location) {
		// TODO check whether location.getIncomingEdges().size()==1 if necessary
		XcfaEdge inEdge = location.getIncomingEdges().get(0);
		builder.removeEdge(inEdge);
		builder.removeLoc(location);

		for (XcfaEdge outEdge : location.getOutgoingEdges()) {
			builder.removeEdge(outEdge);
			List<XcfaLabel> stmts = new ArrayList<>(inEdge.getLabels());
			stmts.addAll(outEdge.getLabels());
			builder.addEdge(XcfaEdge.of(inEdge.getSource(), outEdge.getTarget(), stmts));
		}
	}
}