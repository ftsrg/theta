package hu.bme.mit.theta.xcfa.cat.solver.programs;

import hu.bme.mit.theta.cat.solver.MemoryModelBuilder;
import hu.bme.mit.theta.solver.Solver;

public abstract class Program {
	public abstract void generateProgram(final MemoryModelBuilder builder, final Solver solver);
}
