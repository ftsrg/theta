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

import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public class CallsToFinalLocs extends ProcedurePass {
	private static final List<String> errorFunc = List.of("reach_error");
	private static final List<String> abortFunc = List.of("abort", "exit");
	public boolean postInlining = false;

	private int nameCounter = 0;
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		XcfaLocation errorLoc = XcfaLocation.create(builder.getName() + "_error" + nameCounter++);
		XcfaLocation finalLoc = XcfaLocation.create(builder.getName() + "_final" + nameCounter++);
		builder.addLoc(errorLoc);
		builder.addLoc(finalLoc);
		XcfaLocation oldFinalLoc = builder.getFinalLoc();
		XcfaLocation oldErrorLoc = builder.getErrorLoc();
		builder.setFinalLoc(finalLoc);
		if(oldErrorLoc != null) {
			XcfaEdge toError = XcfaEdge.of(oldErrorLoc, errorLoc, List.of());
			builder.addEdge(toError);
		}
		XcfaEdge toFinal = XcfaEdge.of(oldFinalLoc, finalLoc, List.of());
		builder.addEdge(toFinal);
		builder.setErrorLoc(errorLoc);

		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			Optional<XcfaLabel> e = edge.getLabels().stream().filter(stmt -> stmt instanceof XcfaLabel.ProcedureCallXcfaLabel).findAny();
			if(e.isPresent()) {
				XcfaEdge xcfaEdge;
				String procedure = ((XcfaLabel.ProcedureCallXcfaLabel) e.get()).getProcedure();
				if (errorFunc.contains(procedure)) {
					xcfaEdge = XcfaEdge.of(edge.getSource(), errorLoc, List.of());
				} else if (abortFunc.contains(procedure)) {
					xcfaEdge = XcfaEdge.of(edge.getSource(), finalLoc, List.of());
				} else {
					continue;
				}
				builder.removeEdge(edge);
				builder.addEdge(xcfaEdge);
				FrontendMetadata.lookupMetadata(edge).forEach((s, o) -> {
					FrontendMetadata.create(xcfaEdge, s, o);
				});
			}
		}

		return builder;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}
