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
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class UnusedVarRemovalPass extends ProcedurePass {
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		removeUnusedVars(builder, null);
		return builder;
	}

	public static void removeUnusedVars(XcfaProcedure.Builder builder, Set<VarDecl<?>> usedVars) {
		boolean atLeastOne = true;
		while(atLeastOne) {
			atLeastOne = false;
			Set<VarDecl<?>> vars;
			if(usedVars == null) {
				vars = new LinkedHashSet<>();
				for (XcfaEdge edge : builder.getEdges()) {
					for (Stmt stmt : edge.getStmts()) {
						Set<VarDecl<?>> vars1 = StmtUtils.getVars(stmt);
						vars1.removeIf(varDecl ->
							(
								(stmt instanceof HavocStmt)
								|| (stmt instanceof AssignStmt && ((AssignStmt<?>) stmt).getVarDecl() == varDecl
										&& !builder.getParams().containsKey(((AssignStmt<?>) stmt).getVarDecl()))
							) && builder.getLocalVars().containsKey(varDecl)
						);
						vars.addAll(vars1);
					}
				}
			} else vars = usedVars;
			List<XcfaEdge> edges = new ArrayList<>(builder.getEdges());
			for (int i = 0; i < edges.size(); i++) {
				XcfaEdge edge = edges.get(i);
				List<Stmt> newStmts = new ArrayList<>(edge.getStmts());
				for (Stmt stmt : edge.getStmts()) {
					if (stmt instanceof HavocStmt && !vars.contains(((HavocStmt<?>) stmt).getVarDecl())) {
						newStmts.remove(stmt);
					} else if (stmt instanceof AssignStmt && !vars.contains(((AssignStmt<?>) stmt).getVarDecl())) {
						newStmts.remove(stmt);
					}
				}
				if (newStmts.size() != edge.getStmts().size()) {
					builder.removeEdge(edge);
					XcfaEdge xcfaEdge = new XcfaEdge(edge.getSource(), edge.getTarget(), newStmts);
					builder.addEdge(xcfaEdge);
					FrontendMetadata.lookupMetadata(edge).forEach((s, o) -> {
						FrontendMetadata.create(xcfaEdge, s, o);
					});
					atLeastOne = true;
				}
			}
			List<VarDecl<?>> unused = builder.getLocalVars().keySet().stream().filter(var -> !vars.contains(var)).collect(Collectors.toList());
			for (VarDecl<?> varDecl : unused) {
				builder.getLocalVars().remove(varDecl);
			}
		}
	}
}
