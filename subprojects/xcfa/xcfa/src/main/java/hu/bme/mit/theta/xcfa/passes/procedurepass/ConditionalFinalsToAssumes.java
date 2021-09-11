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

import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.Optional;

public class ConditionalFinalsToAssumes extends ProcedurePass {

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		Optional<XcfaEdge> edgeOpt;
		do {
			edgeOpt = builder.getEdges().stream().filter(
					xcfaEdge -> xcfaEdge.getTarget().isEndLoc() &&
								xcfaEdge.getLabels().stream().anyMatch(stmt -> stmt instanceof XcfaLabel.StmtXcfaLabel && stmt.getStmt() instanceof AssumeStmt) &&
								xcfaEdge.getSource().getOutgoingEdges().size() == 2).findAny();
			edgeOpt.ifPresent(builder::removeEdge);
		} while(edgeOpt.isPresent());
		return builder;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}
