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
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static hu.bme.mit.theta.xcfa.model.XcfaLabel.AtomicBegin;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.AtomicEnd;

public class VerifierFunctionsToLabels extends ProcedurePass {
	private static final String atomicBegin = "__VERIFIER_atomic_begin";
	private static final String atomicEnd = "__VERIFIER_atomic_end";

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			Optional<XcfaLabel> e = edge.getLabels().stream().filter(stmt -> stmt instanceof XcfaLabel.ProcedureCallXcfaLabel && ((XcfaLabel.ProcedureCallXcfaLabel) stmt).getProcedure().startsWith("__VERIFIER")).findAny();
			if(e.isPresent()) {
				List<XcfaLabel> collect = new ArrayList<>();
				for (XcfaLabel label : edge.getLabels()) {
					if(label == e.get()) {
						final String procName = ((XcfaLabel.ProcedureCallXcfaLabel) label).getProcedure();
						if(procName.startsWith("__VERIFIER_nondet")) collect.add(label);
						else {
							switch (procName) {
								case atomicBegin:
									collect.add(AtomicBegin());
									break;
								case atomicEnd:
									collect.add(AtomicEnd());
									break;
								default:
									throw new UnsupportedOperationException("Not yet supported: " + procName);
							}
						}
					}
					else collect.add(label);
				}
				XcfaEdge xcfaEdge;
				xcfaEdge = XcfaEdge.of(edge.getSource(), edge.getTarget(), collect);
				builder.removeEdge(edge);
				builder.addEdge(xcfaEdge);
				FrontendMetadata.lookupMetadata(edge).forEach((s, o) -> {
					FrontendMetadata.create(xcfaEdge, s, o);
				});
			}
		}
		return builder;
	}

	public boolean isPostInlining() {
		return true;
	}

}
