package hu.bme.mit.theta.solver.smtlib.impl.bitwuzla;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSolverFactory;

import java.nio.file.Path;

public class BitwuzlaSmtLibSolverFactory extends GenericSmtLibSolverFactory {
    private BitwuzlaSmtLibSolverFactory(Path solverPath, String[] args) {
        super(solverPath, args);
    }

    public static BitwuzlaSmtLibSolverFactory create(Path solverPath, String[] args) {
        return new BitwuzlaSmtLibSolverFactory(solverPath, args);
    }

    @Override
    public ItpSolver createItpSolver() {
        throw new UnsupportedOperationException("Bitwuzla does not support interpolation");
    }
}
