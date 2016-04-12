package hu.bme.mit.inf.ttmc.solver.z3;

import hu.bme.mit.inf.ttmc.core.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.core.SolverManager;
import hu.bme.mit.inf.ttmc.core.factory.SolverFactory;
import hu.bme.mit.inf.ttmc.solver.z3.factory.Z3SolverFactory;

public class Z3SolverManager implements SolverManager {

	final SolverFactory solverFactory;

	static {
		loadLibraries();
	}

	public Z3SolverManager() {
		solverFactory = new Z3SolverFactory(new ConstraintManagerImpl());
	}

	@Override
	public SolverFactory getSolverFactory() {
		return solverFactory;
	}

	////////

	private static void loadLibraries() {
		System.loadLibrary("msvcr110");
		System.loadLibrary("msvcp110");
		System.loadLibrary("vcomp110");
		System.loadLibrary("libz3");
		System.loadLibrary("libz3java");
	}

}
