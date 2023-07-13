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

import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder;

import java.util.*;
import java.util.stream.Collectors;

public class RemoveDeadEnds implements ProcedurePass {

    // TODO: thread start and procedure call should not be dead-end! Use-case: while(1) pthread_create(..);
    @Override
    public XcfaProcedureBuilder run(XcfaProcedureBuilder builder) {
        if (ArchitectureConfig.multiThreading) {
            Set<XcfaEdge> reachableEdges = new LinkedHashSet<>();
            filterReachableEdges(builder.getInitLoc(), reachableEdges);
            for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
                if (!reachableEdges.contains(edge)) {
                    builder.removeEdge(edge);
                }
            }
            return builder;
        } else {
            if (FrontendMetadata.lookupMetadata("shouldInline", false).size() > 0) return builder;
            Set<XcfaEdge> nonDeadEndEdges = new LinkedHashSet<>();
            Set<XcfaEdge> reachableEdges = new LinkedHashSet<>();
            Optional<XcfaLocation> errorLoc = builder.getErrorLoc();

            Set<XcfaEdge> nonDeadEndFromErrorEdges = new LinkedHashSet<>();
            errorLoc.ifPresent(xcfaLocation -> collectNonDeadEndEdges(xcfaLocation, nonDeadEndFromErrorEdges));

            Set<XcfaEdge> nonDeadEndFromFinalEdges = new LinkedHashSet<>();
            Optional<XcfaLocation> finalLoc = builder.getFinalLoc();
            finalLoc.ifPresent(xcfaLocation -> collectNonDeadEndEdges(xcfaLocation, nonDeadEndFromErrorEdges));

            nonDeadEndEdges.addAll(nonDeadEndFromErrorEdges);
            nonDeadEndEdges.addAll(nonDeadEndFromFinalEdges);

            filterReachableEdges(builder.getInitLoc(), reachableEdges);
            Set<XcfaEdge> collect = builder.getEdges().stream().filter(xcfaEdge -> !nonDeadEndEdges.contains(xcfaEdge)
                    || !reachableEdges.contains(xcfaEdge)).collect(Collectors.toSet());
            for (XcfaEdge edge : collect) {
                builder.removeEdge(edge);
            }
            List<XcfaLocation> toRemove = builder.getLocs().stream().filter(loc -> loc.getIncomingEdges().size() == 0
                    && loc.getOutgoingEdges().size() == 0 && !(loc == builder.getFinalLoc().orElse(null))
                    && !(loc == builder.getErrorLoc().orElse(null))).toList();
            for (XcfaLocation location : toRemove) {
                if (builder.getInitLoc() != location)
                    builder.removeLoc(location);
            }
            return builder;
        }
    }

    private void filterReachableEdges(XcfaLocation loc, Set<XcfaEdge> reachableEdges) {
        Set<XcfaEdge> outgoingEdges = new LinkedHashSet<>(loc.getOutgoingEdges());
        while (!outgoingEdges.isEmpty()) {
            Optional<XcfaEdge> any = outgoingEdges.stream().findAny();
            XcfaEdge outgoingEdge = any.get();
            outgoingEdges.remove(outgoingEdge);
            if (!reachableEdges.contains(outgoingEdge)) {
                reachableEdges.add(outgoingEdge);
                outgoingEdges.addAll(outgoingEdge.getTarget().getOutgoingEdges());
            }
        }
    }

    private void collectNonDeadEndEdges(XcfaLocation loc, Set<XcfaEdge> nonDeadEndEdges) {
        Set<XcfaEdge> incomingEdges = new LinkedHashSet<>(loc.getIncomingEdges());
        while (!incomingEdges.isEmpty()) {
            Optional<XcfaEdge> any = incomingEdges.stream().findAny();
            XcfaEdge incomingEdge = any.get();
            incomingEdges.remove(incomingEdge);
            if (!nonDeadEndEdges.contains(incomingEdge)) {
                nonDeadEndEdges.add(incomingEdge);
                incomingEdges.addAll(incomingEdge.getSource().getIncomingEdges());
            }
        }
    }
}
