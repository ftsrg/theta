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
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.List;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;

public class HavocAssignments extends ProcedurePass {
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		boolean notFound = false;
		while(!notFound) {
			notFound = true;
			Optional<XcfaEdge> havocEdge = builder.getEdges().stream().filter(xcfaEdge ->
					xcfaEdge.getStmts().size() == 1 && xcfaEdge.getStmts().get(0) instanceof HavocStmt &&
					xcfaEdge.getTarget().getIncomingEdges().size() == 1 &&
					xcfaEdge.getTarget().getOutgoingEdges().size() == 1 && xcfaEdge.getTarget().getOutgoingEdges().get(0).getStmts().size() == 1 &&
					xcfaEdge.getTarget().getOutgoingEdges().get(0).getStmts().get(0) instanceof AssignStmt &&
					((AssignStmt<?>) xcfaEdge.getTarget().getOutgoingEdges().get(0).getStmts().get(0)).getExpr() instanceof RefExpr).findAny();
			if(havocEdge.isPresent()) {
				HavocStmt<?> h = (HavocStmt<?>) havocEdge.get().getStmts().get(0);
				XcfaEdge assignEdge = havocEdge.get().getTarget().getOutgoingEdges().get(0);
				AssignStmt<?> a = (AssignStmt<?>) assignEdge.getStmts().get(0);
				if(h.getVarDecl() == ((RefExpr<?>)a.getExpr()).getDecl() && h.getVarDecl().getName().startsWith("call_")) {
					notFound = false;
					builder.removeEdge(havocEdge.get());
					builder.removeEdge(assignEdge);
					XcfaEdge xcfaEdge = new XcfaEdge(havocEdge.get().getSource(), assignEdge.getTarget(), List.of(Havoc(a.getVarDecl())));
					builder.addEdge(xcfaEdge);
					FrontendMetadata.lookupMetadata(assignEdge).forEach((s, o) -> {
						FrontendMetadata.create(xcfaEdge, s, o);
					});
					builder.removeLoc(havocEdge.get().getTarget());
				}
			}
		}
		return builder;
	}
}
