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

package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.*;
import java.util.stream.Collectors;

public class EliminateSelfLoops extends ProcedurePass {
	static final EliminateSelfLoops instance = new EliminateSelfLoops();

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		Set<XcfaEdge> selfLoops = builder.getEdges().stream().filter(xcfaEdge -> xcfaEdge.getSource() == xcfaEdge.getTarget()).collect(Collectors.toSet());
		Map<XcfaLocation, List<XcfaEdge>> locSelfLoops = new HashMap<>();
		for (XcfaEdge selfLoop : selfLoops) {
			List<XcfaEdge> loops = locSelfLoops.getOrDefault(selfLoop.getSource(), new ArrayList<>());
			loops.add(selfLoop);
			locSelfLoops.put(selfLoop.getSource(), loops);
		}
		for (XcfaLocation source : locSelfLoops.keySet()) {
			for (XcfaEdge selfLoop : locSelfLoops.get(source)) builder.removeEdge(selfLoop);
			XcfaLocation target = XcfaLocation.uniqeCopyOf(source);
			builder.addLoc(target);
			for (XcfaEdge selfLoop : locSelfLoops.get(source))
				builder.addEdge(XcfaEdge.of(source, target, selfLoop.getLabels()));
			builder.addEdge(XcfaEdge.of(target, source, List.of()));
		}
		return builder;
	}
}
