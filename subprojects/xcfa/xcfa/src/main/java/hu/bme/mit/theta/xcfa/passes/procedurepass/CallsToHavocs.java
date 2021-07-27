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
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;

public class CallsToHavocs extends ProcedurePass {

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			Optional<Stmt> e = edge.getStmts().stream().filter(stmt -> stmt instanceof XcfaCallStmt).findAny();
			if(e.isPresent()) {
				List<Stmt> collect = new ArrayList<>();
				for (Stmt stmt : edge.getStmts()) {
					if(stmt == e.get()) { // TODO: all _OUT_ params should be havoced!
						Expr<?> expr = ((XcfaCallStmt)e.get()).getParams().get(0);
						checkState(expr instanceof RefExpr && ((RefExpr<?>) expr).getDecl() instanceof VarDecl);
						VarDecl<?> var = (VarDecl<?>) ((RefExpr<?>) expr).getDecl();
						collect.add(Havoc(var));
					}
					else collect.add(stmt);
				}
				XcfaEdge xcfaEdge;
				xcfaEdge = new XcfaEdge(edge.getSource(), edge.getTarget(), collect);
				builder.removeEdge(edge);
				builder.addEdge(xcfaEdge);
				XcfaMetadata.lookupMetadata(edge).forEach((s, o) -> {
					XcfaMetadata.create(xcfaEdge, s, o);
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
