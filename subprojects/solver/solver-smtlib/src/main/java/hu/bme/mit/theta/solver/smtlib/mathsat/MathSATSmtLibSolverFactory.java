package hu.bme.mit.theta.solver.smtlib.mathsat;

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

public class MathSATSmtLibSolverFactory implements SolverFactory {
    private final Path solverPath;
    private final String[] args;
    private final boolean itpSupported;

    private MathSATSmtLibSolverFactory(Path solverPath, String[] args, boolean itpSupported) {
        this.solverPath = solverPath;
        this.args = args;
        this.itpSupported = itpSupported;
    }

    public static MathSATSmtLibSolverFactory create(Path solverPath, String[] args, boolean itpSupported) {
        return new MathSATSmtLibSolverFactory(solverPath, args, itpSupported);
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
        if(itpSupported) {
            final var symbolTable = new GenericSmtLibSymbolTable();
            final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
            final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
            final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args);

            return new MathSATSmtLibItpSolver(symbolTable, transformationManager, termTransformer, solverBinary);
        }
        else {
            throw new UnsupportedOperationException("MathSAT interpolation supported above 5.4.0");
        }
    }
}
