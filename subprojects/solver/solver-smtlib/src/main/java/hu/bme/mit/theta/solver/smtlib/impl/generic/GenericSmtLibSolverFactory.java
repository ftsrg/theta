package hu.bme.mit.theta.solver.smtlib.impl.generic;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolver;

import java.nio.file.Path;

public class GenericSmtLibSolverFactory implements SolverFactory {
    private final Path solverPath;
    private final String[] args;

    private GenericSmtLibSolverFactory(Path solverPath, String[] args) {
        this.solverPath = solverPath;
        this.args = args;
    }

    public static GenericSmtLibSolverFactory create(Path solverPath, String[] args) {
        return new GenericSmtLibSolverFactory(solverPath, args);
    }

    @Override
    public Solver createSolver() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
        final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args);

        return new SmtLibSolver(symbolTable, transformationManager, termTransformer, solverBinary, false);
    }

    @Override
    public UCSolver createUCSolver() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
        final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args);

        return new SmtLibSolver(symbolTable, transformationManager, termTransformer, solverBinary, true);
    }

    @Override
    public ItpSolver createItpSolver() {
        throw new UnsupportedOperationException("GenericSmtLibSolver does not support interpolation");
    }
}
