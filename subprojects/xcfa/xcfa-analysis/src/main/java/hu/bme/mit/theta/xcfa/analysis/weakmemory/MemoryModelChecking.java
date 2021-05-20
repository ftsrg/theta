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

package hu.bme.mit.theta.xcfa.analysis.weakmemory;

import hu.bme.mit.theta.common.LispStringBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.common.datalog.Datalog;
import hu.bme.mit.theta.common.datalog.DatalogArgument;
import hu.bme.mit.theta.common.datalog.GenericDatalogArgument;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.LoadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StoreStmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static hu.bme.mit.theta.common.Utils.lispStringBuilder;

public class MemoryModelChecking {

	private final Map<VarDecl<?>, Tuple2<Map<LoadStmt, XcfaEdge>,Map<StoreStmt, XcfaEdge>>> accessors;

	public MemoryModelChecking(final XCFA xcfa) {
		accessors = new LinkedHashMap<>();
		Datalog datalog = Datalog.createProgram();
		Datalog.Relation po = datalog.createRelation(2);
		Datalog.Relation poPath = datalog.createTransitive(po);
		Datalog.Relation rf = datalog.createRelation(2);
		Datalog.Relation porf = datalog.createDisjunction(Set.of(po, rf));
		Datalog.Relation porfPath = datalog.createTransitive(porf);
		Datalog.Relation coherency = datalog.createRelation(4);
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
								porfPath,
								TupleN.of(w2, r1)
						)
				));

		for (VarDecl<? extends Type> globalVar : xcfa.getGlobalVars()) {
			accessors.put(globalVar, Tuple2.of(new LinkedHashMap<>(), new LinkedHashMap<>()));
		}
		for (XcfaProcess process : xcfa.getProcesses()) {
			for (XcfaProcedure procedure : process.getProcedures()) {
				for (XcfaEdge edge : procedure.getEdges()) {
					List<Stmt> stmts = edge.getStmts();
					for (int i = 0; i < stmts.size(); i++) {
						Stmt stmt = stmts.get(i);
						if (stmt instanceof LoadStmt)
							accessors.get(((LoadStmt) stmt).getGlobal()).get1().put((LoadStmt) stmt, edge);
						else if (stmt instanceof StoreStmt)
							accessors.get(((StoreStmt) stmt).getGlobal()).get2().put((StoreStmt) stmt, edge);

						if (i == 0) {
							for (XcfaEdge incomingEdge : edge.getSource().getIncomingEdges()) {
								Stmt lastStmt = incomingEdge.getStmts().get(incomingEdge.getStmts().size() - 1);
								po.addFact(TupleN.of(GenericDatalogArgument.createArgument(lastStmt), GenericDatalogArgument.createArgument(stmt)));
							}
						} else {
							po.addFact(TupleN.of(GenericDatalogArgument.createArgument(stmts.get(i - 1)), GenericDatalogArgument.createArgument(stmt)));
						}
					}

				}
			}
		}
		for (Map.Entry<VarDecl<?>, Tuple2<Map<LoadStmt, XcfaEdge>, Map<StoreStmt, XcfaEdge>>> entry : accessors.entrySet()) {
			VarDecl<?> varDecl = entry.getKey();
			Tuple2<Map<LoadStmt, XcfaEdge>, Map<StoreStmt, XcfaEdge>> objects = entry.getValue();

			for (LoadStmt loadStmt : objects.get1().keySet()) {
				for (StoreStmt storeStmt : objects.get2().keySet()) {
					rf.addFact(TupleN.of(GenericDatalogArgument.createArgument(storeStmt), GenericDatalogArgument.createArgument(loadStmt)));
				}
			}
		}


		for (TupleN<DatalogArgument> element : coherency.getElements()) {
			System.out.println(lispStringBuilder("coherency").add(element.get(0)).add(element.get(1)).add(element.get(2)).add(element.get(3)));
		}


	}
}
