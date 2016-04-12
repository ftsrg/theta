package hu.bme.mit.inf.ttmc.solver;

public interface SolverFactory {

	public Solver createSolver(final boolean genModels, final boolean genUnsatCores);

	public ItpSolver createItpSolver();

}
