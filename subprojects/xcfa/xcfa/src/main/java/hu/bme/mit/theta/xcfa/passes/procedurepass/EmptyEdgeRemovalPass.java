/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class EmptyEdgeRemovalPass extends ProcedurePass {
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		// removing empty loops (empty edge that has the same source and target) - they are completely unnecessary
		List<XcfaEdge> emptyLoops = builder.getEdges().stream().filter(xcfaEdge -> xcfaEdge.getLabels().size() == 0 && xcfaEdge.getTarget() == xcfaEdge.getSource()).collect(Collectors.toList());
		for (XcfaEdge loop : emptyLoops) {
			builder.removeEdge(loop);
		}

		// removing paralell empty edges
		// (there can be more than two between two given locations and there can be more sets of paralell empty edges going out from a given locations)
		for (XcfaLocation loc : builder.getLocs()) {
			List<XcfaEdge> emptyEdges = loc.getOutgoingEdges().stream().filter(xcfaEdge -> xcfaEdge.getLabels().size() == 0).collect(Collectors.toList());
			List<XcfaEdge> toRemove = new ArrayList<>();

			while(!emptyEdges.isEmpty()) {
				XcfaEdge emptyEdge = emptyEdges.get(0);
				List<XcfaEdge> paralells = loc.getOutgoingEdges().stream().filter(edge -> emptyEdge != edge && emptyEdge.getTarget() == edge.getTarget()).collect(Collectors.toList());
				emptyEdges.remove(emptyEdge);
				emptyEdges.removeAll(paralells);
				toRemove.addAll(paralells);
			}

			for (XcfaEdge paralell : toRemove) {
				builder.removeEdge(paralell);
			}
		}

		boolean found = true;
		while(found) {
			found = false;
			for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
				if (edge.getLabels().size() == 0 && edge.getSource().getOutgoingEdges().size() == 1 && edge.getTarget().getIncomingEdges().size() == 1 &&
					!edge.getTarget().isErrorLoc() && !edge.getTarget().isEndLoc()) {
					builder.removeEdge(edge);
					for (XcfaEdge outgoingEdge : new ArrayList<>(edge.getTarget().getOutgoingEdges())) {
						builder.removeEdge(outgoingEdge);
						builder.addEdge(outgoingEdge.withSource(edge.getSource()));
					}
					found = true;
					break;
				}
			}
		}

		for (XcfaLocation loc : new ArrayList<>(builder.getLocs())) {
			if(loc.getOutgoingEdges().size() == 0 && loc.getIncomingEdges().size() == 0 && !loc.isErrorLoc() && !loc.isEndLoc()) {
				builder.removeLoc(loc);
			}
		}

		return removeEmptySequences(builder);
	}

	// Finding empty sequences (location-empty edge-location-empty edge-...-location)
	// The sequence pattern we use is rather rigorous: starting locations have no other requirements but and outgoing empty edge
	// but the other locations can have no other edges except one incoming and one outgoing empty edge
	// these locations are then merged into the starting location, which means, that one empty edge will remain
	// but this way, if the starting location can start more than one sequence, we can easily merge them all
	private XcfaProcedure.Builder removeEmptySequences(XcfaProcedure.Builder builder) {
		List<XcfaEdge> edgesToStartSequenceOn = builder.getEdges().stream().filter(xcfaEdge -> xcfaEdge.getLabels().size() == 0).collect(Collectors.toList());
		while(edgesToStartSequenceOn.size() != 0) {
			XcfaEdge startEdge = edgesToStartSequenceOn.get(0);
			Set<XcfaLocation> sequence = new LinkedHashSet<>();
			XcfaLocation startingLocation = startEdge.getSource();
			XcfaLocation endLocation = startingLocation;
			sequence.add(startingLocation);

			boolean sequenceEnd = false;
			XcfaEdge currentEdge = startEdge; // the next (possible) edge in the sequence

			while (!sequenceEnd) {
				XcfaLocation nextLocation = currentEdge.getTarget();
				if (hasNoLoops(nextLocation) // has no loop edges
						&& !nextLocation.isEndLoc() // not a final location
						&& !nextLocation.isErrorLoc() // not an error location
						&& hasNIncomingEdge(nextLocation, 1) // has exactly one incoming edge (which is the current edge)
						&& !sequence.contains(nextLocation) // is not already in the sequence
						&& hasNOutgoingEdge(nextLocation, 1) // has exactly one outgoing edge
						&& hasNOutgoingEmptyEdge(nextLocation, 1) // which is empty
				) {
					// the next location can be added to the sequence
					sequence.add(nextLocation);
					endLocation = nextLocation;
				} else {
					// cannot be a part of the sequence - end of sequence BUT without this location
					sequenceEnd = true;
				}

				edgesToStartSequenceOn.remove(currentEdge); // was checked already, we don't want to check it in the future
				if (!sequenceEnd) { // a location was added and has exactly one outgoing edge, which will be the next edge to check
					currentEdge = nextLocation.getOutgoingEdges().stream().filter(xcfaEdge -> xcfaEdge.getLabels().isEmpty()).findFirst().get();
				}
			}

			// merge sequence into it's starting location
			if (sequence.size() > 1) {
				// all (non-empty) edges in the sequence should be moved to the starting location first
				List<XcfaEdge> incomingEdges = new ArrayList<>();
				List<XcfaEdge> outgoingEdges = new ArrayList<>();
				// collect all edges in the sequence (except the starting location, as we will add these edges to that location)
				for (XcfaLocation loc : sequence) {
					if (loc != startingLocation) {
						incomingEdges.addAll(loc.getIncomingEdges());
						outgoingEdges.addAll(loc.getOutgoingEdges());
					}
				}

				// add the outgoing empty edge of the end location to the starting location
				builder.addEdge(XcfaEdge.of(startingLocation, endLocation.getOutgoingEdges().get(0).getTarget(), endLocation.getOutgoingEdges().get(0).getLabels()));

				// remove the old edges and locations
				for (XcfaEdge edge : incomingEdges) {
					builder.removeEdge(edge);
				}
				edgesToStartSequenceOn.removeAll(incomingEdges);

				for (XcfaEdge edge : outgoingEdges) {
					builder.removeEdge(edge);
				}
				edgesToStartSequenceOn.removeAll(outgoingEdges);

				for (XcfaLocation loc : sequence) {
					if (loc != startingLocation) {
						builder.getLocs().remove(loc);
					}
				}
			}

		}
		return builder;
	}

	private boolean hasNOutgoingEmptyEdge(XcfaLocation loc, int n) {
		return loc.getOutgoingEdges().stream().filter(xcfaEdge -> xcfaEdge.getLabels().size() == 0).count() == n;
	}

	private boolean hasNOutgoingEdge(XcfaLocation loc, int n) {
		return loc.getOutgoingEdges().size() == n;
	}

	private boolean hasNIncomingEdge(XcfaLocation loc, int n) {
		return loc.getIncomingEdges().size() == n;
	}

	private boolean hasNoLoops(XcfaLocation loc) {
		return loc.getOutgoingEdges().stream().noneMatch(xcfaEdge -> xcfaEdge.getSource() == xcfaEdge.getTarget());
	}

}