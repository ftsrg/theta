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

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.utils.LabelUtils;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class AssignmentChainRemoval extends ProcedurePass {

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			List<XcfaLabel> newLabels = new ArrayList<>();
			Map<VarDecl<?>, Expr<?>> lastExprs = new LinkedHashMap<>();
			for (XcfaLabel label : edge.getLabels()) {
				VarDecl<?> newVar = null;
				Expr<?> newExpr = null;
				if(label instanceof XcfaLabel.StmtXcfaLabel && label.getStmt() instanceof AssignStmt) {
					Expr<?> lastExpr = ((AssignStmt<?>) label.getStmt()).getExpr();
					VarDecl<?> lastVar = ((AssignStmt<?>) label.getStmt()).getVarDecl();
					if(lastExpr instanceof RefExpr<?> && lastExprs.containsKey((VarDecl<?>) ((RefExpr<?>) lastExpr).getDecl())) {
						newLabels.add(Stmt(Assign(cast(lastVar, lastVar.getType()), cast(lastExprs.get((VarDecl<?>) ((RefExpr<?>)lastExpr).getDecl()), lastVar.getType()))));
						newVar = lastVar;
						newExpr = lastExprs.get((VarDecl<?>) ((RefExpr<?>)lastExpr).getDecl());
					} else {
						newVar = lastVar;
						newExpr = lastExpr;
						newLabels.add(label);
					}
				} else {
					newLabels.add(label);
				}
				final Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> assortedVars = LabelUtils.getAssortedVars(label);
				for (Map.Entry<VarDecl<?>, Expr<?>> entry : new LinkedHashSet<>(lastExprs.entrySet())) {
					VarDecl<?> lastVar = entry.getKey();
					Expr<?> lastExpr = entry.getValue();
					final Set<VarDecl<?>> usedVars = ExprUtils.getVars(lastExpr);
					if(assortedVars.get1().contains(lastVar) || assortedVars.get1().stream().anyMatch(usedVars::contains)) {
						lastExprs.remove(lastVar);
					}
				}
				if(newVar != null && newExpr != null) lastExprs.put(newVar, newExpr);
			}

			builder.removeEdge(edge);
			builder.addEdge(edge.withLabels(newLabels));
		}
		return builder;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}
