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
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;

public class AddAtomicBeginEndsToFunctions extends ProcedurePass {

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		if(builder.getName().startsWith("__VERIFIER_atomic")) {
			for (XcfaEdge outgoingEdge : builder.getInitLoc().getOutgoingEdges()) {
				List<XcfaLabel> labels = new ArrayList<>();
				labels.add(XcfaLabel.AtomicBegin());
				labels.addAll(outgoingEdge.getLabels());
				builder.removeEdge(outgoingEdge);
				builder.addEdge(outgoingEdge.withLabels(labels));
			}
			for (XcfaEdge incomingEdge : builder.getFinalLoc().getIncomingEdges()) {
				List<XcfaLabel> labels = new ArrayList<>(incomingEdge.getLabels());
				labels.add(XcfaLabel.AtomicEnd());
				builder.removeEdge(incomingEdge);
				builder.addEdge(incomingEdge.withLabels(labels));
			}
		}
		return builder;
	}
}
