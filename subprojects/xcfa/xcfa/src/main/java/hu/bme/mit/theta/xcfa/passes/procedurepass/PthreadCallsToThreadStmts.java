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
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.Reference;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.JoinThread;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.StartThread;

public class PthreadCallsToThreadStmts extends ProcedurePass {
	private static final String threadStart = "pthread_create";
	private static final int threadStartHandle = 0;
	private static final int threadStartFuncPtr = 2;
	private static final int threadStartParam = 3;
	private static final String threadJoin = "pthread_join";
	private static final int threadJoinHandle = 0;

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		boolean foundAny = false;
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			Optional<XcfaLabel> e = edge.getLabels().stream().filter(stmt -> stmt instanceof XcfaLabel.ProcedureCallXcfaLabel && ((XcfaLabel.ProcedureCallXcfaLabel) stmt).getProcedure().startsWith("pthread_")).findAny();
			if(e.isPresent()) {
				List<XcfaLabel> collect = new ArrayList<>();
				for (XcfaLabel label : edge.getLabels()) {
					if(label == e.get()) {
						switch(((XcfaLabel.ProcedureCallXcfaLabel) label).getProcedure()){
							case threadStart:
								Expr<?> handle = ((XcfaLabel.ProcedureCallXcfaLabel) label).getParams().get(threadStartHandle + 1);
								while(handle instanceof Reference) handle = ((Reference<?, ?>) handle).getOp();
								checkState(handle instanceof RefExpr && ((RefExpr<?>) handle).getDecl() instanceof VarDecl);
								Expr<?> funcptr = ((XcfaLabel.ProcedureCallXcfaLabel) label).getParams().get(threadStartFuncPtr + 1);
								checkState(funcptr instanceof RefExpr && ((RefExpr<?>) funcptr).getDecl() instanceof VarDecl);
								Expr<?> param = ((XcfaLabel.ProcedureCallXcfaLabel) label).getParams().get(threadStartParam + 1);
								XcfaLabel.StartThreadXcfaLabel startThreadStmt = StartThread((VarDecl<?>) ((RefExpr<?>) handle).getDecl(), ((RefExpr<?>) funcptr).getDecl().getName(), param);
								collect.add(startThreadStmt);
								foundAny = true;
								break;
							case threadJoin:
								handle = ((XcfaLabel.ProcedureCallXcfaLabel) label).getParams().get(threadJoinHandle + 1);
								while(handle instanceof Reference) handle = ((Reference<?, ?>) handle).getOp();
								checkState(handle instanceof RefExpr && ((RefExpr<?>) handle).getDecl() instanceof VarDecl);
								XcfaLabel.JoinThreadXcfaLabel joinThreadStmt = JoinThread((VarDecl<?>) ((RefExpr<?>) handle).getDecl());
								collect.add(joinThreadStmt);
								foundAny = true;
								break;
							default:
								throw new UnsupportedOperationException("Not yet supported: " + ((XcfaLabel.ProcedureCallXcfaLabel) label).getProcedure());
						}
					}
					else collect.add(label);
				}
				XcfaEdge xcfaEdge;
				xcfaEdge = XcfaEdge.of(edge.getSource(), edge.getTarget(), collect);
				builder.removeEdge(edge);
				builder.addEdge(xcfaEdge);
				FrontendMetadata.lookupMetadata(edge).forEach((s, o) -> {
					FrontendMetadata.create(xcfaEdge, s, o);
				});
			}
		}
		if(foundAny) {
			ArchitectureConfig.multiThreading = true;
		}
		return builder;
	}
}
