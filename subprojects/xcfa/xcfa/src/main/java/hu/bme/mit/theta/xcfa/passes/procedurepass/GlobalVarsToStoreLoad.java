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
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.utils.XcfaLabelVarReplacer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Load;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Store;
import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.getVars;

public class GlobalVarsToStoreLoad extends ProcedurePass {

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		if(!ArchitectureConfig.multiThreading) return builder;
		Map<VarDecl<?>, VarDecl<?>> varLut = new LinkedHashMap<>();
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			Set<XcfaLabel> collect = edge.getLabels().stream().filter(stmt1 -> !(stmt1 instanceof XcfaLabel.LoadXcfaLabel) && !(stmt1 instanceof XcfaLabel.StoreXcfaLabel) && getVars(stmt1).stream().anyMatch(
					varDecl -> !builder.getLocalVars().containsKey(varDecl) && !builder.getParams().containsKey(varDecl)
			)).collect(Collectors.toSet());
			for(XcfaLabel stmt : collect) {
				Set<VarDecl<?>> vars = getVars(stmt).stream().filter(
						varDecl -> !varLut.containsKey(varDecl) && !builder.getLocalVars().containsKey(varDecl) && !builder.getParams().containsKey(varDecl)
				).collect(Collectors.toSet());
				for (VarDecl<?> var : vars) {
					VarDecl<?> newVar = Var(var.getName() + "_local", var.getType());
					varLut.put(var, newVar);
					if(FrontendMetadata.getMetadataValue(var.getRef(), "cType").isPresent())FrontendMetadata.create(newVar.getRef(), "cType", CComplexType.getType(var.getRef()));
					builder.createVar(newVar, null);
				}
			}

			List<XcfaLabel> stmts = new ArrayList<>();
			for (XcfaLabel edgeStmt : edge.getLabels()) {
				stmts.addAll(collectLoadStores(edgeStmt, varLut));
			}
			builder.removeEdge(edge);
			XcfaEdge xcfaEdge = XcfaEdge.of(edge.getSource(), edge.getTarget(), stmts);
			FrontendMetadata.lookupMetadata(edge).forEach((s, o) -> FrontendMetadata.create(xcfaEdge, s, o));
			builder.addEdge(xcfaEdge);

		}

		return builder;
	}

	private Collection<? extends XcfaLabel> collectLoadStores(XcfaLabel edgeStmt, Map<VarDecl<?>, VarDecl<?>> varLut) {
		List<XcfaLabel> loads = new ArrayList<>();
		List<XcfaLabel> stores = new ArrayList<>();
		XcfaLabel newEdgeStmt = edgeStmt.accept(new XcfaLabelVarReplacer(), varLut);
		if(!getVars(edgeStmt).containsAll(getVars(newEdgeStmt))) {
			if (edgeStmt instanceof XcfaLabel.StmtXcfaLabel && edgeStmt.getStmt() instanceof AssignStmt &&
					newEdgeStmt instanceof XcfaLabel.StmtXcfaLabel && newEdgeStmt.getStmt() instanceof AssignStmt) {
				if (varLut.containsKey(((AssignStmt<?>) edgeStmt.getStmt()).getVarDecl())) {
					stores.add(Store(((AssignStmt<?>) newEdgeStmt.getStmt()).getVarDecl(), ((AssignStmt<?>) edgeStmt.getStmt()).getVarDecl(), false, ""));
				}
				ExprUtils.getVars(((AssignStmt<?>) edgeStmt.getStmt()).getExpr()).stream().filter(varLut::containsKey).forEach(varDecl ->
						loads.add(Load(varDecl, varLut.get(varDecl), false, "")));
			}
			else if(edgeStmt instanceof XcfaLabel.StmtXcfaLabel && edgeStmt.getStmt() instanceof HavocStmt && varLut.containsKey(((HavocStmt<?>) edgeStmt.getStmt()).getVarDecl())) {
				stores.add(Store(varLut.get(((HavocStmt<?>) edgeStmt.getStmt()).getVarDecl()), ((HavocStmt<?>) edgeStmt.getStmt()).getVarDecl(), false, ""));
			}
			else {
				getVars(edgeStmt).stream().filter(varLut::containsKey).forEach(varDecl ->
						loads.add(Load(varDecl, varLut.get(varDecl), false, "")));
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
