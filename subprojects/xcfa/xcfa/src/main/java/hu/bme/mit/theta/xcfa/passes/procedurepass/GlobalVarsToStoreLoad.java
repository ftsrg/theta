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
import hu.bme.mit.theta.core.stmt.xcfa.LoadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StoreStmt;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.utils.XcfaLabelVarReplacer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;

public class GlobalVarsToStoreLoad extends ProcedurePass {

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		Map<VarDecl<?>, VarDecl<?>> varLut = new LinkedHashMap<>();
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			Set<Stmt> collect = edge.getLabels().stream().filter(stmt1 -> !(stmt1 instanceof LoadStmt) && !(stmt1 instanceof StoreStmt) && StmtUtils.getVars(stmt1).stream().anyMatch(
					varDecl -> !builder.getLocalVars().containsKey(varDecl) && !builder.getParams().containsKey(varDecl)
			)).collect(Collectors.toSet());
			for(Stmt stmt : collect) {
				Set<VarDecl<?>> vars = StmtUtils.getVars(stmt).stream().filter(
						varDecl -> !varLut.containsKey(varDecl) && !builder.getLocalVars().containsKey(varDecl) && !builder.getParams().containsKey(varDecl)
				).collect(Collectors.toSet());
				for (VarDecl<?> var : vars) {
					VarDecl<?> newVar = Var(var.getName() + "_local", var.getType());
					varLut.put(var, newVar);
					builder.createVar(newVar, null);
				}
			}

			List<Stmt> stmts = new ArrayList<>();
			for (Stmt edgeStmt : edge.getLabels()) {
				stmts.addAll(collectLoadStores(edgeStmt, varLut));
			}
			builder.removeEdge(edge);
			XcfaEdge xcfaEdge = XcfaEdge.of(edge.getSource(), edge.getTarget(), stmts);
			FrontendMetadata.lookupMetadata(edge).forEach((s, o) -> FrontendMetadata.create(xcfaEdge, s, o));
			builder.addEdge(xcfaEdge);

		}

		return builder;
	}

	private Collection<? extends Stmt> collectLoadStores(Stmt edgeStmt, Map<VarDecl<?>, VarDecl<?>> varLut) {
		List<Stmt> loads = new ArrayList<>();
		List<Stmt> stores = new ArrayList<>();
		Stmt newEdgeStmt = edgeStmt.accept(new XcfaLabelVarReplacer(), varLut);
		if(!StmtUtils.getVars(edgeStmt).containsAll(StmtUtils.getVars(newEdgeStmt))) {
			if (edgeStmt instanceof AssignStmt && newEdgeStmt instanceof AssignStmt) {
				if (varLut.containsKey(((AssignStmt<?>) edgeStmt).getVarDecl())) {
					stores.add(new StoreStmt(((AssignStmt<?>) newEdgeStmt).getVarDecl(), ((AssignStmt<?>) edgeStmt).getVarDecl(), false, ""));
				}
				ExprUtils.getVars(((AssignStmt<?>) edgeStmt).getExpr()).stream().filter(varLut::containsKey).forEach(varDecl ->
						loads.add(new LoadStmt(varDecl, varLut.get(varDecl), false, "")));
			}
			else if(edgeStmt instanceof HavocStmt && varLut.containsKey(((HavocStmt<?>) edgeStmt).getVarDecl())) {
				stores.add(new StoreStmt(varLut.get(((HavocStmt<?>) edgeStmt).getVarDecl()), ((HavocStmt<?>) edgeStmt).getVarDecl(), false, ""));
			}
			else {
				StmtUtils.getVars(edgeStmt).stream().filter(varLut::containsKey).forEach(varDecl ->
						loads.add(new LoadStmt(varDecl, varLut.get(varDecl), false, "")));
			}
		}
		loads.add(newEdgeStmt);
		loads.addAll(stores);
		return loads;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}
