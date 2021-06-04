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
import java.util.List;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;

public class EmptyEdgeRemovalPass implements ProcedurePass {
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		boolean notFound = false;
		while(!notFound) {
			notFound = true;
			Optional<XcfaEdge> edge = builder.getEdges().stream().filter(xcfaEdge ->
					   xcfaEdge.getStmts().size() == 0
					&& xcfaEdge.getTarget() != xcfaEdge.getSource()
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
			Optional<XcfaLocation> loc = builder.getLocs().stream().filter(xcfaLocation -> builder.getInitLoc() != xcfaLocation && builder.getFinalLoc() != xcfaLocation && xcfaLocation.getIncomingEdges().stream().filter(xcfaEdge -> xcfaEdge.getSource() != xcfaEdge.getTarget()).findAny().isEmpty()).findFirst();
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

		return builder;
	}
}
