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
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class CallsToHavocs extends ProcedurePass {

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		boolean found = true;
		while(found) {
			found = false;
			for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
				Optional<XcfaLabel> e = edge.getLabels().stream().filter(stmt -> stmt instanceof XcfaLabel.ProcedureCallXcfaLabel && FrontendMetadata.getMetadataValue(((XcfaLabel.ProcedureCallXcfaLabel) stmt).getProcedure(), "ownFunction").isPresent() && !(Boolean) FrontendMetadata.getMetadataValue(((XcfaLabel.ProcedureCallXcfaLabel) stmt).getProcedure(), "ownFunction").get()).findAny();
				if (e.isPresent()) {
					List<XcfaLabel> collect = new ArrayList<>();
					for (XcfaLabel stmt : edge.getLabels()) {
						if (stmt == e.get()) { // TODO: all _OUT_ params should be havoced!
							if(!((XcfaLabel.ProcedureCallXcfaLabel)e.get()).getProcedure().startsWith("__VERIFIER_nondet")) {
								throw new UnsupportedOperationException("Non-nondet function call used as nondet!");
							}
							Expr<?> expr = ((XcfaLabel.ProcedureCallXcfaLabel) e.get()).getParams().get(0);
							checkState(expr instanceof RefExpr && ((RefExpr<?>) expr).getDecl() instanceof VarDecl);
							VarDecl<?> var = (VarDecl<?>) ((RefExpr<?>) expr).getDecl();
							if(!(CComplexType.getType(var.getRef()) instanceof CVoid)) {
								final HavocStmt<?> havoc = Havoc(var);
								FrontendMetadata.lookupMetadata(stmt).forEach((s, o) -> FrontendMetadata.create(havoc, s, o));
								collect.add(Stmt(havoc));
							}
						} else collect.add(stmt);
					}
					XcfaEdge xcfaEdge;
					xcfaEdge = XcfaEdge.of(edge.getSource(), edge.getTarget(), collect);
					builder.removeEdge(edge);
					builder.addEdge(xcfaEdge);
					found = true;
					FrontendMetadata.lookupMetadata(edge).forEach((s, o) -> {
						FrontendMetadata.create(xcfaEdge, s, o);
					});
				}
			}
		}

		return builder;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}