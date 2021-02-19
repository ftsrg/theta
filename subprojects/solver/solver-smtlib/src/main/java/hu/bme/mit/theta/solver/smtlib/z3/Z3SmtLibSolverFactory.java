package hu.bme.mit.theta.solver.smtlib.z3;

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

public class Z3SmtLibSolverFactory implements SolverFactory {
    private final Path solverPath;
    private final String[] args;

    private Z3SmtLibSolverFactory(Path solverPath, String[] args) {
        this.solverPath = solverPath;
        this.args = args;
    }

    public static Z3SmtLibSolverFactory create(Path solverPath, String[] args) {
        return new Z3SmtLibSolverFactory(solverPath, args);
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
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
        final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args);

        return new Z3SmtLibItpSolver(symbolTable, transformationManager, termTransformer, solverBinary);
    }
}
