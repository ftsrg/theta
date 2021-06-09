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

import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.List;
import java.util.Optional;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class AssignmentChainRemoval extends ProcedurePass {
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		boolean notFound = false;
		while(!notFound) {
			notFound = true;
			Optional<XcfaEdge> assignEdge1 = builder.getEdges().stream().filter(xcfaEdge ->
					xcfaEdge.getStmts().size() == 1 && xcfaEdge.getStmts().get(0) instanceof AssignStmt &&
					xcfaEdge.getTarget().getIncomingEdges().size() == 1 &&
					xcfaEdge.getTarget().getOutgoingEdges().size() == 1 && xcfaEdge.getTarget().getOutgoingEdges().get(0).getStmts().size() == 1 &&
					xcfaEdge.getTarget().getOutgoingEdges().get(0).getStmts().get(0) instanceof AssignStmt &&
					((AssignStmt<?>) xcfaEdge.getTarget().getOutgoingEdges().get(0).getStmts().get(0)).getExpr() instanceof RefExpr).findAny();
			if(assignEdge1.isPresent()) {
				AssignStmt<?> a1 = (AssignStmt<?>) assignEdge1.get().getStmts().get(0);
				XcfaEdge assignEdge = assignEdge1.get().getTarget().getOutgoingEdges().get(0);
				AssignStmt<?> a2 = (AssignStmt<?>) assignEdge.getStmts().get(0);
				if(a1.getVarDecl() == ((RefExpr<?>)a2.getExpr()).getDecl() && a1.getVarDecl().getName().startsWith("call_")) {
					notFound = false;
					builder.removeEdge(assignEdge1.get());
					builder.removeEdge(assignEdge);
					XcfaEdge xcfaEdge = new XcfaEdge(
							assignEdge1.get().getSource(),
							assignEdge.getTarget(),
							List.of(
									Assign(
											cast(a2.getVarDecl(), a2.getVarDecl().getType()),
											cast(a1.getExpr(), a2.getVarDecl().getType()))));
					builder.addEdge(xcfaEdge);
					XcfaMetadata.lookupMetadata(assignEdge).forEach((s, o) -> {
						XcfaMetadata.create(xcfaEdge, s, o);
					});
					builder.getLocs().remove(assignEdge1.get().getTarget());
				}
			}
		}
		return builder;
	}
}
