package hu.bme.mit.theta.solver.z3;

public class ContextInterrupt {
	public static void interruptContexts() {
		if(Z3Solver.currentContext!=null) {
			Z3Solver.currentContext.interrupt();
		}
		if(Z3ItpSolver.currentContext!=null) {
			Z3ItpSolver.currentContext.interrupt();
		}
	}
}
