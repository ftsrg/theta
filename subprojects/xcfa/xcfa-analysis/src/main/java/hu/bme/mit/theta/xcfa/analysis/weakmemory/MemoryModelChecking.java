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
import java.util.Map;
import java.util.Set;

public class MemoryModelChecking {

	private final Map<VarDecl<?>, Tuple2<Map<LoadStmt, XcfaProcess>,Map<StoreStmt, XcfaProcess>>> accessors;

	public MemoryModelChecking(final XCFA xcfa) {
		accessors = new LinkedHashMap<>();
		Datalog datalog = Datalog.createProgram();
		Datalog.Relation po = datalog.createRelation(2);
		Datalog.Relation poPath = datalog.createTransitive(po);
		Datalog.Relation rf = datalog.createRelation(2);
		Datalog.Relation porf = datalog.createDisjunction(Set.of(po, rf));
		Datalog.Relation porfPath = datalog.createTransitive(porf);
		for (VarDecl<? extends Type> globalVar : xcfa.getGlobalVars()) {
			accessors.put(globalVar, Tuple2.of(new LinkedHashMap<>(), new LinkedHashMap<>()));
		}
		for (XcfaProcess process : xcfa.getProcesses()) {
			for (XcfaProcedure procedure : process.getProcedures()) {
				for (XcfaEdge edge : procedure.getEdges()) {
					for (Stmt stmt : edge.getStmts()) {
						if(stmt instanceof LoadStmt) accessors.get(((LoadStmt) stmt).getGlobal()).get1().put((LoadStmt) stmt, process);
						else if(stmt instanceof StoreStmt) accessors.get(((StoreStmt) stmt).getGlobal()).get2().put((StoreStmt) stmt, process);
					}
					po.addFact(TupleN.of(GenericDatalogArgument.createArgument(edge.getSource()), GenericDatalogArgument.createArgument(edge.getTarget())));
				}
			}
		}

	}
}
