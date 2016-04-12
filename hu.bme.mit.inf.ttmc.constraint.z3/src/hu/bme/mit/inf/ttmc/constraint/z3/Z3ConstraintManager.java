package hu.bme.mit.inf.ttmc.constraint.z3;

import hu.bme.mit.inf.ttmc.constraint.z3.factory.Z3SolverFactory;
import hu.bme.mit.inf.ttmc.core.ConstraintManager;
import hu.bme.mit.inf.ttmc.core.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.core.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.core.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.core.factory.SolverFactory;
import hu.bme.mit.inf.ttmc.core.factory.TypeFactory;

public class Z3ConstraintManager implements ConstraintManager {

	final ConstraintManager manager;
	final SolverFactory solverFactory;

	static {
		loadLibraries();
	}

	public Z3ConstraintManager() {
		manager = new ConstraintManagerImpl();
		solverFactory = new Z3SolverFactory(manager);
	}

	@Override
	public DeclFactory getDeclFactory() {
		return manager.getDeclFactory();
	}

	@Override
	public TypeFactory getTypeFactory() {
		return manager.getTypeFactory();
	}

	@Override
	public ExprFactory getExprFactory() {
		return manager.getExprFactory();
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
