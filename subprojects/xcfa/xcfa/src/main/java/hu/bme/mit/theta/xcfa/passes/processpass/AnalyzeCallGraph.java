/*
 *  Copyright 2022 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.xcfa.passes.processpass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.*;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class AnalyzeCallGraph extends ProcessPass {
	@Override
	public XcfaProcess.Builder run(XcfaProcess.Builder builder) {
		Map<XcfaProcedure.Builder, Set<XcfaProcedure.Builder>> calledBy = new LinkedHashMap<>();
		for (XcfaProcedure.Builder procedure : builder.getProcedures()) {
			calledBy.put(procedure, new LinkedHashSet<>());
		}

		for (XcfaProcedure.Builder procedure : builder.getProcedures()) {
			List<XcfaEdge> edgesToAdd = new ArrayList<>();
			List<XcfaEdge> edgesToRemove = new ArrayList<>();
			for (XcfaEdge edge : procedure.getEdges()) {
				for (XcfaLabel label : edge.getLabels()) {
					if (label instanceof XcfaLabel.ProcedureCallXcfaLabel) {
						XcfaLabel.ProcedureCallXcfaLabel callLabel = (XcfaLabel.ProcedureCallXcfaLabel) label;
						Optional<XcfaProcedure.Builder> procedureOpt = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(callLabel.getProcedure())).findAny();
						if (procedureOpt.isPresent()) {
							XcfaProcedure.Builder calledProcedure = procedureOpt.get();
							calledBy.get(calledProcedure).add(procedure);
							if (calledProcedure.getRetType() != null) {
								XcfaLocation middle = XcfaLocation.uniqeCopyOf(edge.getSource());
								procedure.addLoc(middle);
								edgesToRemove.add(edge);
								edgesToAdd.add(XcfaEdge.of(edge.getSource(), middle, edge.getLabels()));
								List<XcfaLabel> retStmts = new ArrayList<>();
								int paramCnt = 0;
								for (Map.Entry<VarDecl<?>, XcfaProcedure.Direction> entry : calledProcedure.getParams().entrySet()) {
									VarDecl<?> varDecl = entry.getKey();
									XcfaProcedure.Direction direction = entry.getValue();
									if (direction != XcfaProcedure.Direction.IN) {
										Expr<?> expr = callLabel.getParams().get(paramCnt);
										checkState(expr instanceof RefExpr && ((RefExpr<?>) expr).getDecl() instanceof VarDecl<?>);
										retStmts.add(Stmt(Assign(cast((VarDecl<?>) ((RefExpr<?>) expr).getDecl(), varDecl.getType()), cast(varDecl.getRef(), varDecl.getType()))));
									}
									++paramCnt;
								}
								XcfaEdge retEdge = XcfaEdge.of(middle, edge.getTarget(), retStmts);
								FrontendMetadata.lookupMetadata(edge).forEach((s, o) -> {
									FrontendMetadata.create(retEdge, s, o);
								});
								edgesToAdd.add(retEdge);
							}
						} else {
							FrontendMetadata.create(callLabel.getProcedure(), "ownFunction", false);
						}
					}
				}
			}
			edgesToRemove.forEach(procedure::removeEdge);
			edgesToAdd.forEach(procedure::addEdge);
		}

		boolean done = false;
		while (!done) {
			done = true;
			for (Map.Entry<XcfaProcedure.Builder, Set<XcfaProcedure.Builder>> entry : calledBy.entrySet()) {
				Set<XcfaProcedure.Builder> callers = entry.getValue();
				for (XcfaProcedure.Builder caller : new LinkedHashSet<>(callers)) {
					Set<XcfaProcedure.Builder> newCallers = calledBy.get(caller);
					if (!callers.containsAll(newCallers)) {
						done = false;
					}
					callers.addAll(newCallers);
				}
			}
		}

		FrontendMetadata.lookupMetadata("shouldInline", false).stream().filter(o -> o instanceof String).collect(Collectors.toList()).forEach(o -> {
			final Optional<XcfaProcedure.Builder> any = builder.getProcedures().stream().filter(builder1 -> builder1.getName().equals(o)).findAny();
			FrontendMetadata.create(any.get(), "shouldKeep", true);
		});

		calledBy.forEach((procedure, xcfaProcedures) -> {
			if (xcfaProcedures.contains(procedure)) {
				FrontendMetadata.create(procedure, "shouldInline", false);
			}
		});

		return builder;
	}
}
