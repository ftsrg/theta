package hu.bme.mit.inf.ttmc.solver.z3;

import hu.bme.mit.inf.ttmc.core.ConstraintManager;
import hu.bme.mit.inf.ttmc.solver.ItpSolver;
import hu.bme.mit.inf.ttmc.solver.Solver;
import hu.bme.mit.inf.ttmc.solver.SolverManager;
import hu.bme.mit.inf.ttmc.solver.z3.solver.Z3ItpSolver;
import hu.bme.mit.inf.ttmc.solver.z3.solver.Z3Solver;
import hu.bme.mit.inf.ttmc.solver.z3.trasform.Z3SymbolTable;
import hu.bme.mit.inf.ttmc.solver.z3.trasform.Z3TermTransformer;
import hu.bme.mit.inf.ttmc.solver.z3.trasform.Z3TransformationManager;

public class Z3SolverManager implements SolverManager {

	static {
		loadLibraries();
	}

	////////

	private static void loadLibraries() {
		System.loadLibrary("msvcr110");
		System.loadLibrary("msvcp110");
		System.loadLibrary("vcomp110");
		System.loadLibrary("libz3");
		System.loadLibrary("libz3java");
	}

	///////

	final ConstraintManager manager;

	final com.microsoft.z3.InterpolationContext z3Context;

	final Z3SymbolTable symbolTable;

	public Z3SolverManager(final ConstraintManager manager) {
		this.manager = manager;
		z3Context = new com.microsoft.z3.InterpolationContext();
		symbolTable = new Z3SymbolTable();
	}

	@Override
	public Solver createSolver(final boolean genModels, final boolean genUnsatCores) {
		final com.microsoft.z3.Solver z3Solver = z3Context.mkSimpleSolver();
		final Z3TransformationManager transformationManager = new Z3TransformationManager(symbolTable, z3Context);
		final Z3TermTransformer termTransformer = new Z3TermTransformer(manager.getExprFactory(), symbolTable);
		return new Z3Solver(transformationManager, termTransformer, z3Context, z3Solver);
	}

	@Override
	public ItpSolver createItpSolver() {
		final com.microsoft.z3.Solver z3Solver = z3Context.mkSimpleSolver();
		final Z3TransformationManager transformationManager = new Z3TransformationManager(symbolTable, z3Context);
		final Z3TermTransformer termTransformer = new Z3TermTransformer(manager.getExprFactory(), symbolTable);
		return new Z3ItpSolver(transformationManager, termTransformer, z3Context, z3Solver);
	}

}
