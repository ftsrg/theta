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

public class EmptyEdgeRemovalPass extends ProcedurePass {
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		// removing empty loops (edge that has the same source and target) - they are completely unnecessary
		List<XcfaEdge> emptyLoops = builder.getEdges().stream().filter(xcfaEdge -> xcfaEdge.getStmts().size() == 0 && xcfaEdge.getTarget() == xcfaEdge.getSource()).collect(Collectors.toList());
		for (XcfaEdge loop : emptyLoops) {
			builder.removeEdge(loop);
		}

		// removing paralell empty edges
		List<XcfaEdge> emptyEdges = builder.getEdges().stream().filter(xcfaEdge -> xcfaEdge.getStmts().size() == 0).collect(Collectors.toList());
		List<XcfaEdge> paralellsToRemove = new ArrayList<>();
		List<XcfaEdge> paralellsToRemain = new ArrayList<>();
		for (XcfaEdge emptyEdge : emptyEdges) {
			if(!paralellsToRemain.contains(emptyEdge)) {
				for (XcfaEdge emptyEdge1 : emptyEdges) {
					if(emptyEdge != emptyEdge1
					  && emptyEdge.getSource() == emptyEdge1.getSource()
					  && emptyEdge.getTarget() == emptyEdge1.getTarget()) {
						paralellsToRemain.add(emptyEdge1);
						paralellsToRemove.add(emptyEdge);
					}
				}
			}
		}
		for (XcfaEdge paralellEdge : paralellsToRemove) {
			builder.removeEdge(paralellEdge);
		}

		// finding empty edge sequences and merging them into a single location, but with a few other requirements:
		// - the locations included cannot come up twice while walking on the sequence
		//   (no loops on the locations and no cycles of the locations in the sequence)
		// - the locations included cannot have any other outgoing or incoming empty edges except those in the sequence
		//   (the algorithm would merge those in another step, but that can easily lead to false transformations)
		List<XcfaEdge> edgesToStartSequenceOn = builder.getEdges().stream().filter(xcfaEdge -> xcfaEdge.getStmts().size() == 0).collect(Collectors.toList());
		while(edgesToStartSequenceOn.size() != 0) {
			XcfaEdge startEdge = edgesToStartSequenceOn.get(0);
			Set<XcfaLocation> sequence = new HashSet<>();
			sequence.add(startEdge.getSource());

			boolean sequenceEnd = false;
			XcfaEdge currentEdge = startEdge;
			// TODO check startedge for reqs as well
			// TODO final/error loc should not be in sequence! (it will most likely be removed that way)
			while(!sequenceEnd) {
				edgesToStartSequenceOn.remove(currentEdge); // either it fits into the sequence and we'll remove it or it does not fit into the sequence and a seq. cannot be started on it
				ArrayList<XcfaEdge> targetOutgoingEdges = new ArrayList<>(currentEdge.getTarget().getOutgoingEdges());
				// target should not have any loop edges
				if(targetOutgoingEdges.stream().filter(xcfaEdge -> xcfaEdge.getSource() == xcfaEdge.getTarget()).count() == 0) {
					List<XcfaEdge> targetOutgoingEmptyEdges = targetOutgoingEdges.stream().filter(xcfaEdge -> xcfaEdge.getStmts().size() == 0).collect(Collectors.toList());
					// target should have exactly one incoming empty edge (the current edge)
					if(currentEdge.getTarget().getIncomingEdges().stream().filter(xcfaEdge -> xcfaEdge.getStmts().size() == 0).count() == 1) {
						// target should have exactly one outgoing empty edge
						if(targetOutgoingEmptyEdges.size() == 1) {
							// target should not be part of a cycle in the sequence
							if(!sequence.contains(currentEdge.getTarget())) {
								// add target to the sequence
								sequence.add(currentEdge.getTarget());
								currentEdge = targetOutgoingEmptyEdges.get(0);
							} else {
								// end of sequence (without target)
								sequenceEnd = true;
							}
						} else if (targetOutgoingEmptyEdges.size() == 0) {
							// if it has 0 then it is the end of the sequence (including target)
							sequence.add(currentEdge.getTarget());
							currentEdge = targetOutgoingEmptyEdges.get(0);
							sequenceEnd = true;
						} else {
							// end of sequence (without target)
							sequenceEnd = true;
						}
					} else {
						// end of sequence (without target)
						sequenceEnd = true;
					}
				} else {
					// end of sequence (without target)
					sequenceEnd = true;
				}
			}

			if(sequence.size()>2) {
				// merge sequence into it's start location
				List<XcfaEdge> incomingEdges = new ArrayList<>();
				List<XcfaEdge> outgoingEdges = new ArrayList<>();
				// collect all edges in the sequence (except the starting location, as we will add these edges to that location)
				for (XcfaLocation loc : sequence) {
					if(loc != startEdge.getSource()) {
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

				// remove the edges and the locations
				for (XcfaEdge edge : incomingEdges) {
					builder.removeEdge(edge);
				}

				for (XcfaEdge edge : outgoingEdges) {
					builder.removeEdge(edge);
				}

				for (XcfaLocation loc : sequence) {
					if(loc!=startEdge.getSource()) {
						builder.getLocs().remove(loc);
					}
				}
			}
		}

		return builder;
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
