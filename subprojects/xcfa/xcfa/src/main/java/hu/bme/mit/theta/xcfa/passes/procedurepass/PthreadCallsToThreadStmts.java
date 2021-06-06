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
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.stmt.xcfa.JoinThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StartThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;

public class PthreadCallsToThreadStmts extends ProcedurePass {
	private static final String threadStart = "pthread_create";
	private static final int threadStartHandle = 0;
	private static final int threadStartFuncPtr = 2;
	private static final int threadStartParam = 3;
	private static final String threadJoin = "pthread_join";
	private static final int threadJoinHandle = 0;

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			Optional<Stmt> e = edge.getStmts().stream().filter(stmt -> stmt instanceof XcfaCallStmt && ((XcfaCallStmt) stmt).getProcedure().startsWith("pthread_")).findAny();
			if(e.isPresent()) {
				List<Stmt> collect = new ArrayList<>();
				for (Stmt stmt : edge.getStmts()) {
					if(stmt == e.get()) {
						switch(((XcfaCallStmt) stmt).getProcedure()){
							case threadStart:
								Expr<?> handle = ((XcfaCallStmt) stmt).getParams().get(threadStartHandle + 1);
								checkState(handle instanceof RefExpr && ((RefExpr<?>) handle).getDecl() instanceof VarDecl);
								Expr<?> funcptr = ((XcfaCallStmt) stmt).getParams().get(threadStartFuncPtr + 1);
								checkState(funcptr instanceof RefExpr && ((RefExpr<?>) handle).getDecl() instanceof VarDecl);
								Expr<?> param = ((XcfaCallStmt) stmt).getParams().get(threadStartParam + 1);
								StartThreadStmt startThreadStmt = new StartThreadStmt(((RefExpr<?>) handle).getDecl().getName(), ((RefExpr<?>) funcptr).getDecl().getName(), param);
								collect.add(startThreadStmt);
								break;
							case threadJoin:
								handle = ((XcfaCallStmt) stmt).getParams().get(threadJoinHandle + 1);
								checkState(handle instanceof RefExpr && ((RefExpr<?>) handle).getDecl() instanceof VarDecl);
								JoinThreadStmt joinThreadStmt = new JoinThreadStmt(((RefExpr<?>) handle).getDecl().getName());
								collect.add(joinThreadStmt);
								break;
							default:
								throw new UnsupportedOperationException("Not yet supported: " + ((XcfaCallStmt) stmt).getProcedure());
						}
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
}
