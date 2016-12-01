package hu.bme.mit.theta.solver;

public interface SolverFactory {

	Solver createSolver();

	ItpSolver createItpSolver();

}
