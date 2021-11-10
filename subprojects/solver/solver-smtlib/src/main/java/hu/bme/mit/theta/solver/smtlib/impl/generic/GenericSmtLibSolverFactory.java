package hu.bme.mit.theta.solver.smtlib.impl.generic;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolver;

import java.nio.file.Path;

public class GenericSmtLibSolverFactory implements SolverFactory {
    protected final Path solverPath;
    protected final String[] args;
    private final boolean isCvc4;

    protected GenericSmtLibSolverFactory(Path solverPath, String[] args) {
        this(solverPath, args, false);
    }

    protected GenericSmtLibSolverFactory(Path solverPath, String[] args, boolean isCvc4) {
        this.solverPath = solverPath;
        this.args = args;
        this.isCvc4 = isCvc4;
    }

    public static GenericSmtLibSolverFactory create(Path solverPath, String[] args) {
        return new GenericSmtLibSolverFactory(solverPath, args);
    }

    @Override
    public Solver createSolver() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
        final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args, isCvc4);

        return new SmtLibSolver(symbolTable, transformationManager, termTransformer, solverBinary, false);
    }

    @Override
    public UCSolver createUCSolver() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
        final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args, isCvc4);

        return new SmtLibSolver(symbolTable, transformationManager, termTransformer, solverBinary, true);
    }

    @Override
    public ItpSolver createItpSolver() {
        throw new UnsupportedOperationException("The generic driver does not support interpolation");
    }
}
