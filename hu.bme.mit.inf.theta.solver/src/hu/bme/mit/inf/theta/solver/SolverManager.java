package hu.bme.mit.inf.theta.solver;

public interface SolverManager {

	public Solver createSolver(final boolean genModels, final boolean genUnsatCores);

	public ItpSolver createItpSolver();

}
