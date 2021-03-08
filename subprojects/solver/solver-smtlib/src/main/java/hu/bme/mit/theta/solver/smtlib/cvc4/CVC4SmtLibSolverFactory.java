package hu.bme.mit.theta.solver.smtlib.cvc4;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolver;
import hu.bme.mit.theta.solver.smtlib.generic.GenericSmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.generic.GenericSmtLibTransformationManager;

import java.nio.file.Path;

public class CVC4SmtLibSolverFactory implements SolverFactory {
    private final Path solverPath;
    private final String[] args;

    private CVC4SmtLibSolverFactory(Path solverPath, String[] args) {
        this.solverPath = solverPath;
        this.args = args;
    }

    public static CVC4SmtLibSolverFactory create(Path solverPath, String[] args) {
        return new CVC4SmtLibSolverFactory(solverPath, args);
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
        throw new UnsupportedOperationException("CVC4 does not support interpolation");
    }
}
