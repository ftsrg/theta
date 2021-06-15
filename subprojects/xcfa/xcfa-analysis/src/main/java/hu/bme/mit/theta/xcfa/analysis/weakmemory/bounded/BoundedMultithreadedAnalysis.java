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

package hu.bme.mit.theta.xcfa.analysis.weakmemory.bounded;

import hu.bme.mit.theta.common.LispStringBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.common.datalog.Datalog;
import hu.bme.mit.theta.common.datalog.DatalogArgument;
import hu.bme.mit.theta.common.datalog.GenericDatalogArgument;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.FenceStmt;
import hu.bme.mit.theta.core.stmt.xcfa.JoinThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.LoadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StartThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StoreStmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.model.XcfaState;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.common.Utils.lispStringBuilder;

public class BoundedMultithreadedAnalysis {

	private final Map<VarDecl<?>, Tuple2<Map<LoadStmt, XcfaEdge>, Map<StoreStmt, XcfaEdge>>> accessors;
	private final Datalog.Relation r;
	private final Datalog.Relation w;
	private final Datalog.Relation f;
	private final Datalog.Relation po;

	public BoundedMultithreadedAnalysis(final XCFA xcfa) {
		Datalog datalog = Datalog.createProgram();
		r = datalog.createRelation("r",2);
		w = datalog.createRelation("w",2);
		f = datalog.createRelation("f",1);
		po = datalog.createRelation("po",2);
		Datalog.Relation poPath = datalog.createTransitive("poPath", po);
		Datalog.Relation rf = datalog.createRelation("rf", 2);
		Datalog.Relation porf = datalog.createDisjunction("porf", Set.of(po, rf));
		Datalog.Relation porfPath = datalog.createTransitive("porfPath", porf);
		Datalog.Relation coherency = datalog.createRelation("coherency", 4);
		Datalog.Variable w1, w2, r1, r2;
		coherency.addRule(TupleN.of(
				w1 = datalog.getVariable(),
				w2 = datalog.getVariable(),
				r1 = datalog.getVariable(),
				r2 = datalog.getVariable()
			),
				Set.of(
						Tuple2.of(
								porfPath,
								TupleN.of(w1, w2)
						),
						Tuple2.of(
								porfPath,
								TupleN.of(r1, r2)
						),
						Tuple2.of(
								rf,
								TupleN.of(w1, r2)
						),
						Tuple2.of(
								rf,
								TupleN.of(w2, r1)
						)
				));

		accessors = new LinkedHashMap<>();
		for (VarDecl<? extends Type> globalVar : xcfa.getGlobalVars()) {
			accessors.put(globalVar, Tuple2.of(new LinkedHashMap<>(), new LinkedHashMap<>()));
		}
		XcfaProcedure mainProcedure = xcfa.getMainProcess().getMainProcedure();
		walkXcfaLoc(mainProcedure.getInitLoc(), xcfa.getMainProcess(), mainProcedure, mainProcedure.getInitLoc());

		accessors.forEach((varDecl, objects) -> {
			objects.get1().forEach((loadStmt, xcfaEdge) -> {
				objects.get2().forEach((storeStmt, xcfaEdge1) -> {
					rf.addFact(TupleN.of(GenericDatalogArgument.createArgument(loadStmt), GenericDatalogArgument.createArgument(storeStmt)));
				});
			});
		});

		ExecutionGraphPrinter.print(datalog);
	}

	private final Set<Tuple2<Object, Object>> edges = new LinkedHashSet<>();
	private void walkXcfaLoc(Object lastNode, XcfaProcess process, XcfaProcedure procedure, XcfaLocation loc) {
//		if(loc.getIncomingEdges().size() > 1) {
//			if(edges.contains(Tuple2.of(lastNode, loc))) return;
//			edges.add(Tuple2.of(lastNode, loc));
//			po.addFact(TupleN.of(GenericDatalogArgument.createArgument(lastNode), GenericDatalogArgument.createArgument(loc)));
//			lastNode = loc;
//		}
		for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
			walkXcfaEdge(lastNode, process, procedure, outgoingEdge);
		}
	}
	private void walkXcfaEdge(Object lastNode, XcfaProcess process, XcfaProcedure procedure, XcfaEdge edge) {
		checkState(edge.getStmts().size() == 1, "Exactly 1 instruction per edge is necessary.");
		Stmt stmt = edge.getStmts().get(0);
		boolean shouldAdd = false;
		if (stmt instanceof LoadStmt) {
			accessors.get(((LoadStmt) stmt).getGlobal()).get1().put((LoadStmt) stmt, edge);
			r.addFact(TupleN.of(GenericDatalogArgument.createArgument(stmt), GenericDatalogArgument.createArgument(((LoadStmt) stmt).getGlobal())));
			shouldAdd = true;
		} else if (stmt instanceof StoreStmt) {
			accessors.get(((StoreStmt) stmt).getGlobal()).get2().put((StoreStmt) stmt, edge);
			w.addFact(TupleN.of(GenericDatalogArgument.createArgument(stmt), GenericDatalogArgument.createArgument(((StoreStmt) stmt).getGlobal())));
			shouldAdd = true;
		} else if (stmt instanceof FenceStmt) {
			f.addFact(TupleN.of(GenericDatalogArgument.createArgument(stmt)));
			shouldAdd = true;
		} else if (stmt instanceof StartThreadStmt) {
			Optional<XcfaProcedure> callee = process.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(((StartThreadStmt) stmt).getThreadName())).findFirst();
			checkState(callee.isPresent());
			walkXcfaLoc(lastNode, process, callee.get(), callee.get().getInitLoc());
		}

		if(shouldAdd) {
			if(edges.contains(Tuple2.of(lastNode, stmt))) return;
			edges.add(Tuple2.of(lastNode, stmt));
			po.addFact(TupleN.of(GenericDatalogArgument.createArgument(lastNode), GenericDatalogArgument.createArgument(stmt)));
			lastNode = stmt;
		}
		walkXcfaLoc(lastNode, process, procedure, edge.getTarget());
	}
}
