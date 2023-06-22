package hu.bme.mit.theta.solver.smtlib.impl.princess;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSolverFactory;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager;

import java.nio.file.Path;
import java.util.EnumSet;

public class PrincessSmtLibSolverFactory extends GenericSmtLibSolverFactory {
    private PrincessSmtLibSolverFactory(Path solverPath, String[] args) {
        super(solverPath, args, EnumSet.of(GenericSmtLibSolverBinary.Solver.PRINCESS));
    }

    public static PrincessSmtLibSolverFactory create(Path solverPath, String[] args) {
        return new PrincessSmtLibSolverFactory(solverPath, args);
    }

    @Override
    public ItpSolver createItpSolver() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
        final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args, EnumSet.of(GenericSmtLibSolverBinary.Solver.PRINCESS));

        return new PrincessSmtLibItpSolver(symbolTable, transformationManager, termTransformer, solverBinary);
    }
}
