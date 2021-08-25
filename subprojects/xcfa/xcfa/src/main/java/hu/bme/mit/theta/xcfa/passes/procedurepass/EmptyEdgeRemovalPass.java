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
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class EmptyEdgeRemovalPass extends ProcedurePass {
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		// removing empty loops (edge that has the same source and target) - they are completely unnecessary
		List<XcfaEdge> emptyLoops = builder.getEdges().stream().filter(xcfaEdge -> xcfaEdge.getStmts().size() == 0 && xcfaEdge.getTarget() == xcfaEdge.getSource()).collect(Collectors.toList());
		for (XcfaEdge loop : emptyLoops) {
			builder.removeEdge(loop);
		}

		// removing paralell empty edges
		// (there can be more than two between two given locations and there can be more sets of paralell empty edges going out from a given locations)
		for (XcfaLocation loc : builder.getLocs()) {
			List<XcfaEdge> emptyEdges = loc.getOutgoingEdges().stream().filter(xcfaEdge -> xcfaEdge.getStmts().size() == 0).collect(Collectors.toList());
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

		return removeEmptySequences(builder);
	}

	// finding empty sequences (location-empty edge-location-empty edge-...-location) and merging them into a single location, but with a few other requirements:
	// - the locations included cannot come up twice while walking on the sequence
	//   (no loops on the locations and no cycles of the locations in the sequence)
	// - the locations included cannot have any other outgoing or incoming empty edges except those in the sequence
	//   (the algorithm would merge those in another step, but that can easily lead to false transformations)
	// - the locations included cannot be final/error locs (if they are in the sequence they will be removed, except if they start the sequence, but that would not make much sense)
	private XcfaProcedure.Builder removeEmptySequences(XcfaProcedure.Builder builder) {
		List<XcfaEdge> edgesToStartSequenceOn = builder.getEdges().stream().filter(xcfaEdge -> xcfaEdge.getStmts().size() == 0).collect(Collectors.toList());
		while(edgesToStartSequenceOn.size() != 0) {
			XcfaEdge startEdge = edgesToStartSequenceOn.get(0);
			Set<XcfaLocation> sequence = new HashSet<>();
			XcfaLocation startingLocation = startEdge.getSource();
			if (!(hasNoLoops(startingLocation)
					&& !startingLocation.isEndLoc()
					&& !startingLocation.isErrorLoc()
					&& hasNOutgoingEmptyEdge(startingLocation, 1)
					// the starting location may have 0 incoming empty edges as well, as it starts the sequence
					&& (hasNIncomingEmptyEdge(startingLocation, 0) || hasNIncomingEmptyEdge(startingLocation, 1)))) {
				// not a valid sequence starter
				edgesToStartSequenceOn.remove(startEdge);
			} else { // valid location and edge to start the sequence on
				sequence.add(startEdge.getSource());
				boolean sequenceEnd = false;
				XcfaEdge currentEdge = startEdge; // the next (possible) edge in the sequence

				while (!sequenceEnd) {
					XcfaLocation nextLocation = currentEdge.getTarget();
					if (hasNoLoops(nextLocation) // has no loop edges
							&& !nextLocation.isEndLoc() // not a final location
							&& !nextLocation.isErrorLoc() // not an error location
							&& hasNIncomingEmptyEdge(nextLocation, 1) // has exactly one incoming empty edge
							&& !sequence.contains(nextLocation) // is not already in the sequence
					) {
						if (hasNOutgoingEmptyEdge(nextLocation, 1)) { // has exactly one outgoing empty edge
							// it can be the next location of the sequence
							sequence.add(nextLocation);
						} else if (hasNOutgoingEmptyEdge(nextLocation, 0)) { // ha no outgoing empty edge
							// this location is the end location of the sequence
							sequence.add(nextLocation);
							sequenceEnd = true;
						} else {
							// cannot be a part of the sequence - end of sequence BUT without this location
							sequenceEnd = true;
						}
					} else {
						// cannot be a part of the sequence - end of sequence BUT without this location
						sequenceEnd = true;
					}

					if (!sequenceEnd) { // a location was added and has exactly one outgoing edge, which will be the next edge to check
						edgesToStartSequenceOn.remove(currentEdge); // was checked already, we don't want to check it in the future
						currentEdge = nextLocation.getOutgoingEdges().stream().filter(xcfaEdge -> xcfaEdge.getStmts().isEmpty()).findFirst().get();
					}
				}

				if (sequence.size() > 1) {
					// merge sequence into it's starting location

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
					// filter out the empty edges
					List<XcfaEdge> incomingNonEmptyEdges = incomingEdges.stream().filter(xcfaEdge -> !xcfaEdge.getStmts().isEmpty()).collect(Collectors.toList());
					List<XcfaEdge> outgoingNonEmptyEdges = outgoingEdges.stream().filter(xcfaEdge -> !xcfaEdge.getStmts().isEmpty()).collect(Collectors.toList());

					// add the edges to the starting location of the sequence
					for (XcfaEdge edge : incomingNonEmptyEdges) {
						// TODO we basically lose metadata here (and above as well) - turn the pass (or most of it) off, if that's a problem
						XcfaEdge newEdge = new XcfaEdge(edge.getSource(), startEdge.getSource(), edge.getStmts());
						builder.addEdge(newEdge);
					}

					for (XcfaEdge edge : outgoingNonEmptyEdges) {
						// TODO we basically lose metadata here (and above as well) - turn the pass (or most of it) off, if that's a problem
						new XcfaEdge(startEdge.getSource(), edge.getTarget(), edge.getStmts());
					}

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
		}
		return builder;
	}

	private boolean hasNOutgoingEmptyEdge(XcfaLocation loc, int n) {
		return loc.getOutgoingEdges().stream().filter(xcfaEdge -> xcfaEdge.getStmts().size() == 0).count() == n;
	}

	private boolean hasNIncomingEmptyEdge(XcfaLocation loc, int n) {
		return loc.getIncomingEdges().stream().filter(xcfaEdge -> xcfaEdge.getStmts().size() == 0).count() == n;
	}

	private boolean hasNoLoops(XcfaLocation loc) {
		return loc.getOutgoingEdges().stream().noneMatch(xcfaEdge -> xcfaEdge.getSource() == xcfaEdge.getTarget());
	}

	/*
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		boolean notFound = false;
		while(!notFound) {
			notFound = true;
			Optional<XcfaEdge> edge = builder.getEdges().stream().filter(xcfaEdge ->
					   xcfaEdge.getStmts().size() == 0
					&& xcfaEdge.getTarget() != xcfaEdge.getSource() // TODO delete empty loops, don't just ignore them?
					&& !xcfaEdge.getTarget().isEndLoc()
					&& !xcfaEdge.getTarget().isErrorLoc()
			).findFirst();
			if(edge.isPresent()) {
				notFound = false;
				List<XcfaEdge> outgoingEdges = new ArrayList<>(edge.get().getTarget().getOutgoingEdges());
				for (XcfaEdge xcfaEdge : outgoingEdges) {
					if(xcfaEdge.getTarget() == xcfaEdge.getSource()) {
						XcfaEdge e = new XcfaEdge(edge.get().getSource(), edge.get().getSource(), xcfaEdge.getStmts());
						builder.addEdge(e);
						XcfaMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
							XcfaMetadata.create(e, s, o);
						});
					}
					else {
						XcfaEdge e = new XcfaEdge(edge.get().getSource(), xcfaEdge.getTarget(), xcfaEdge.getStmts());
						builder.addEdge(e);
						XcfaMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
							XcfaMetadata.create(e, s, o);
						});
					}
				}
				builder.removeEdge(edge.get());
			}
		}

		notFound = false;
		while(!notFound) {
			notFound = true;
			Optional<XcfaLocation> loc = builder.getLocs().stream().filter(
					xcfaLocation -> builder.getInitLoc() != xcfaLocation && builder.getFinalLoc() != xcfaLocation
							&& xcfaLocation.getIncomingEdges().stream().filter(xcfaEdge -> xcfaEdge.getSource() != xcfaEdge.getTarget()).findAny().isEmpty()).findFirst();
			if(loc.isPresent()) {
				notFound = false;
				List<XcfaEdge> outgoingEdges = new ArrayList<>(loc.get().getOutgoingEdges());
				for (XcfaEdge outgoingEdge : outgoingEdges) {
					builder.removeEdge(outgoingEdge);
				}
				builder.getLocs().remove(loc.get());
			}
		}

		notFound = false;
		while(!notFound) {
			notFound = true;
			Optional<XcfaEdge> duplicateEdge = builder.getEdges().stream().
					filter(xcfaEdge ->
							xcfaEdge.getStmts().size() == 0 &&
									builder.getEdges().stream().anyMatch(xcfaEdge1 ->
											xcfaEdge != xcfaEdge1 &&
											xcfaEdge1.getSource() == xcfaEdge.getSource() &&
											xcfaEdge1.getTarget() == xcfaEdge.getTarget() &&
											xcfaEdge1.getStmts().size() == 0)).
					findAny();
			if(duplicateEdge.isPresent()) {
				notFound = false;
				builder.removeEdge(duplicateEdge.get());
			}
		}

		for (XcfaEdge incomingEdge : new LinkedHashSet<>(builder.getFinalLoc().getIncomingEdges())) {
			if(incomingEdge.getStmts().size() == 0) {
				XcfaLocation source = incomingEdge.getSource();
				for (XcfaEdge edge : new LinkedHashSet<>(source.getIncomingEdges())) {
					builder.removeEdge(edge);
					builder.addEdge(new XcfaEdge(edge.getSource(), builder.getFinalLoc(), edge.getStmts()));
				}
				builder.removeEdge(incomingEdge);
			}
		}

		return builder;
	}
	 */

	@Override
	public boolean isPostInlining() {
		return true;
	}
}
