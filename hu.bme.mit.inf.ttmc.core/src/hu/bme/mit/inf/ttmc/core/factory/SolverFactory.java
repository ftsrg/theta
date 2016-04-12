package hu.bme.mit.inf.ttmc.core.factory;

import hu.bme.mit.inf.ttmc.core.solver.ItpSolver;
import hu.bme.mit.inf.ttmc.core.solver.Solver;

public interface SolverFactory {

	public Solver createSolver(final boolean genModels, final boolean genUnsatCores);

	public ItpSolver createItpSolver();

}
