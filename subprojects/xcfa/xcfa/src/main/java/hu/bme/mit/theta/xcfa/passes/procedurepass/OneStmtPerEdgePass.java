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

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static hu.bme.mit.theta.core.stmt.Stmts.Skip;

public class OneStmtPerEdgePass extends ProcedurePass {
	private static int tmpcnt = 0;
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		boolean notFound = false;
		while(!notFound) {
			notFound = true;
			Optional<XcfaEdge> edge = builder.getEdges().stream().filter(xcfaEdge -> xcfaEdge.getStmts().size() == 0).findFirst();
			if(edge.isPresent()) {
				notFound = false;
				XcfaEdge xcfaEdge = new XcfaEdge(edge.get().getSource(), edge.get().getTarget(), List.of(Skip()));
				builder.addEdge(xcfaEdge);
				FrontendMetadata.lookupMetadata(edge.get()).forEach((s, o) -> FrontendMetadata.create(xcfaEdge, s, o));
				builder.removeEdge(edge.get());
			}
			edge = builder.getEdges().stream().filter(xcfaEdge -> xcfaEdge.getStmts().size() > 1).findFirst();
			if(edge.isPresent()) {
				notFound = false;
				XcfaLocation lastLoc = edge.get().getSource(), interLoc;
				for (Stmt stmt : edge.get().getStmts()) {
					interLoc = edge.get().getStmts().indexOf(stmt) == edge.get().getStmts().size() - 1 ? edge.get().getTarget() : new XcfaLocation("tmp_" + tmpcnt++, Map.of());
					builder.addLoc(interLoc);
					FrontendMetadata.create(edge.get(), "xcfaInterLoc", interLoc);
					XcfaEdge xcfaEdge = new XcfaEdge(lastLoc, interLoc, List.of(stmt));
					lastLoc = interLoc;
					builder.addEdge(xcfaEdge);
					FrontendMetadata.lookupMetadata(edge.get()).forEach((s, o) -> FrontendMetadata.create(xcfaEdge, s, o));
				}
				builder.removeEdge(edge.get());
			}
		}

		return builder;
	}
}
