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

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public class CallsToFinalLocs implements ProcedurePass {
	private static final String errorFunc = "reach_error";

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		XcfaLocation errorLoc = new XcfaLocation("error", Map.of());
		XcfaLocation finalLoc = new XcfaLocation("final", Map.of());
		builder.addLoc(errorLoc);
		builder.addLoc(finalLoc);
		XcfaLocation oldFinalLoc = builder.getFinalLoc();
		builder.setFinalLoc(finalLoc);
		XcfaEdge toFinal = new XcfaEdge(oldFinalLoc, finalLoc, List.of());
		builder.addEdge(toFinal);
		builder.setErrorLoc(errorLoc);

		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			Optional<Stmt> e = edge.getStmts().stream().filter(stmt -> stmt instanceof XcfaCallStmt).findAny();
			if(e.isPresent()) {
				builder.removeEdge(edge);
				XcfaEdge xcfaEdge = new XcfaEdge(edge.getSource(), ((XcfaCallStmt)e.get()).getProcedure().equals(errorFunc) ? errorLoc : finalLoc, List.of());
				builder.addEdge(xcfaEdge);
				XcfaMetadata.lookupMetadata(edge).forEach((s, o) -> {
					XcfaMetadata.create(xcfaEdge, s, o);
				});
			}
		}

		return builder;
	}
}
