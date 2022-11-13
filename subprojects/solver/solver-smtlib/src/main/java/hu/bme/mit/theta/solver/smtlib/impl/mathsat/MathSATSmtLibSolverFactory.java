package hu.bme.mit.theta.solver.smtlib.impl.mathsat;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSolverFactory;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolver;

import java.nio.file.Path;

public class MathSATSmtLibSolverFactory extends GenericSmtLibSolverFactory {
	private final boolean itpSupported;

	private MathSATSmtLibSolverFactory(Path solverPath, String[] args, boolean itpSupported) {
		super(solverPath, args);
		this.itpSupported = itpSupported;
	}

	public static MathSATSmtLibSolverFactory create(Path solverPath, String[] args, boolean itpSupported) {
		return new MathSATSmtLibSolverFactory(solverPath, args, itpSupported);
	}

	@Override
	public Solver createSolver() {
		final var symbolTable = new GenericSmtLibSymbolTable();
		final var transformationManager = new MathSATSmtLibTransformationManager(symbolTable);
		final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
		final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args);

		return new SmtLibSolver(symbolTable, transformationManager, termTransformer, solverBinary, false);
	}

	@Override
	public UCSolver createUCSolver() {
		final var symbolTable = new GenericSmtLibSymbolTable();
		final var transformationManager = new MathSATSmtLibTransformationManager(symbolTable);
		final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
		final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args);

		return new SmtLibSolver(symbolTable, transformationManager, termTransformer, solverBinary, true);
	}

	@Override
	public ItpSolver createItpSolver() {
		if (itpSupported) {
			final var symbolTable = new GenericSmtLibSymbolTable();
			final var transformationManager = new MathSATSmtLibTransformationManager(symbolTable);
			final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
			final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args);

			return new MathSATSmtLibItpSolver(symbolTable, transformationManager, termTransformer, solverBinary);
		} else {
			throw new UnsupportedOperationException("MathSAT interpolation supported above 5.4.0");
		}
	}
}
