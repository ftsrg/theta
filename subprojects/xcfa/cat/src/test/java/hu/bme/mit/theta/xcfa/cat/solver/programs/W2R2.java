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

package hu.bme.mit.theta.xcfa.cat.solver.programs;

import hu.bme.mit.theta.cat.solver.MemoryModelBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

import java.util.List;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class W2R2 extends Program {
	@Override
	public void generateProgram(final MemoryModelBuilder builder, final Solver solver) {
		final String start = "start";
		final String thr1 = "thr1";
		final String thr2 = "thr2";
		final String var = "var";
		final String write1 = "write1";
		final String write2 = "write2";
		final String read1 = "read1";
		final String read2 = "read2";

		builder.addProgramLoc(start);
		builder.addProgramLoc(thr1);
		builder.addProgramLoc(thr2);
		builder.addProgramLoc(var);
		builder.addWriteProgramLoc(write1, thr1, var);
		builder.addWriteProgramLoc(write2, thr1, var);
		builder.addReadProgramLoc(read1, thr2, var);
		builder.addReadProgramLoc(read2, thr2, var);
		builder.addPoEdge(start, write1);
		builder.addPoEdge(start, read1);
		builder.addPoEdge(read1, read2);
		builder.addPoEdge(write1, write2);

		final List<Tuple2<?, ConstDecl<?>>> writes = List.of(Tuple2.of(write1, Const(write1, Int())), Tuple2.of(write2, Const(write2, Int())));
		final List<Tuple2<?, ConstDecl<?>>> reads = List.of(Tuple2.of(read1, Const(read1, Int())), Tuple2.of(read2, Const(read2, Int())));

		solver.add(builder.addConstraints(writes, reads));

		final Expr<BoolType> and = And(List.of(
				Eq(writes.get(0).get2().getRef(), Int(1)),
				Eq(writes.get(1).get2().getRef(), Int(2)),
				Eq(reads.get(0).get2().getRef(), Int(2)),
				Eq(reads.get(1).get2().getRef(), Int(1))
		));
		solver.add(and);
	}
}
