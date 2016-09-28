package hu.bme.mit.theta.solver.z3;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.z3.trasform.Z3SymbolTable;
import hu.bme.mit.theta.solver.z3.trasform.Z3TermTransformer;
import hu.bme.mit.theta.solver.z3.trasform.Z3TransformationManager;

public final class Z3SolverFactory implements SolverFactory {

	private static final Z3SolverFactory INSTACE;

	static {
		loadLibraries();
		INSTACE = new Z3SolverFactory();
	}

	private Z3SolverFactory() {
	}

	public static Z3SolverFactory getInstace() {
		return INSTACE;
	}

	private static void loadLibraries() {
		switch (OsHelper.getOs()) {
		case WINDOWS:
			System.loadLibrary("libz3");
			System.loadLibrary("libz3java");
			break;
		case LINUX:
			System.loadLibrary("z3");
			System.loadLibrary("z3java");
			break;
		default:
			throw new RuntimeException("Operating system not supported.");
		}
	}

	@Override
	public Solver createSolver() {
		final com.microsoft.z3.Context z3Context = new com.microsoft.z3.Context();
		final com.microsoft.z3.Solver z3Solver = z3Context.mkSimpleSolver();

		final Z3SymbolTable symbolTable = new Z3SymbolTable();
		final Z3TransformationManager transformationManager = new Z3TransformationManager(symbolTable, z3Context);
		final Z3TermTransformer termTransformer = new Z3TermTransformer(symbolTable);

		return new Z3Solver(symbolTable, transformationManager, termTransformer, z3Context, z3Solver);
	}

	@Override
	public ItpSolver createItpSolver() {
		final com.microsoft.z3.InterpolationContext z3Context = new com.microsoft.z3.InterpolationContext();
		final com.microsoft.z3.Solver z3Solver = z3Context.mkSimpleSolver();

		final Z3SymbolTable symbolTable = new Z3SymbolTable();
		final Z3TransformationManager transformationManager = new Z3TransformationManager(symbolTable, z3Context);
		final Z3TermTransformer termTransformer = new Z3TermTransformer(symbolTable);

		return new Z3ItpSolver(symbolTable, transformationManager, termTransformer, z3Context, z3Solver);
	}

}
