package hu.bme.mit.theta.solver;

public interface SolverFactory {

	public Solver createSolver();

	public ItpSolver createItpSolver();

}
