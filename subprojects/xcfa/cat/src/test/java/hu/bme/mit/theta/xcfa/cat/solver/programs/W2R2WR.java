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

public class W2R2WR extends Program{
	@Override
	public void generateProgram(final MemoryModelBuilder builder, final Solver solver) {
		final String start = "start";
		final String thr = "main";
		final String thr1 = "thr1";
		final String thr2 = "thr2";
		final String var1 = "var1";
		final String var2 = "var2";
		final String write1 = "write1";
		final String write2 = "write2";
		final String write3 = "write3";
		final String read1 = "read1";
		final String read2 = "read2";
		final String read3 = "read3";

		builder.addProgramLoc(start);
		builder.addProgramLoc(thr);
		builder.addProgramLoc(thr1);
		builder.addProgramLoc(thr2);
		builder.addProgramLoc(var1);
		builder.addProgramLoc(var2);
		builder.addWriteProgramLoc(write1, thr1, var1);
		builder.addWriteProgramLoc(write2, thr1, var1);
		builder.addWriteProgramLoc(write3, thr2, var2);
		builder.addReadProgramLoc(read1, thr2, var1);
		builder.addReadProgramLoc(read2, thr2, var1);
		builder.addReadProgramLoc(read3, thr, var2);
		builder.addPoEdge(start, write1);
		builder.addPoEdge(start, read1);
		builder.addPoEdge(start, read3);
		builder.addPoEdge(read1, read2);
		builder.addPoEdge(write1, write2);
		builder.addPoEdge(read2, write3);

		final List<Tuple2<?, ConstDecl<?>>> writes = List.of(Tuple2.of(write1, Const(write1, Int())), Tuple2.of(write2, Const(write2, Int())), Tuple2.of(write3, Const(write3, Int())));
		final List<Tuple2<?, ConstDecl<?>>> reads = List.of(Tuple2.of(read1, Const(read1, Int())), Tuple2.of(read2, Const(read2, Int())), Tuple2.of(read3, Const(read3, Int())));

		solver.add(builder.addConstraints(writes, reads));

		final Expr<BoolType> and =  And(List.of(
				Eq(writes.get(0).get2().getRef(), Int(1)),
				Eq(writes.get(1).get2().getRef(), Int(2)),
				Eq(reads.get(0).get2().getRef(), Int(2)),
				Eq(reads.get(1).get2().getRef(), Int(1)),
				Eq(writes.get(2).get2().getRef(), Int(3)),
				Eq(reads.get(2).get2().getRef(), Int(3))
		));
		solver.add(and);
	}
}
