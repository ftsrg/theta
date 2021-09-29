package hu.bme.mit.theta.solver.z3;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverBase;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.UCSolver;

import java.util.HashSet;
import java.util.Set;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public final class Z3SolverManager extends SolverManager {
    private static final String NAME = "Z3";

    private boolean closed = false;
    private final Set<SolverBase> instantiatedSolvers = new HashSet<>();

    private Z3SolverManager() {}

    public static Z3SolverManager create() {
        return new Z3SolverManager();
    }

    @Override
    public boolean managesSolver(final String name) {
        return NAME.equals(name);
    }

    @Override
    public SolverFactory getSolverFactory(final String name) {
        checkArgument(NAME.equals(name));
        return new ManagedFactory(Z3SolverFactory.getInstance());
    }

    @Override
    public synchronized void close() throws Exception {
        for(final var solver : instantiatedSolvers) {
            solver.close();
        }
        closed = true;
    }

    private final class ManagedFactory implements SolverFactory {
        private final SolverFactory solverFactory;

        private ManagedFactory(final SolverFactory solverFactory) {
            this.solverFactory = solverFactory;
        }

        @Override
        public Solver createSolver() {
            checkState(!closed, "Solver manager was closed");
            final var solver = solverFactory.createSolver();
            instantiatedSolvers.add(solver);
            return solver;
        }

        @Override
        public UCSolver createUCSolver() {
            checkState(!closed, "Solver manager was closed");
            final var solver = solverFactory.createUCSolver();
            instantiatedSolvers.add(solver);
            return solver;
        }

        @Override
        public ItpSolver createItpSolver() {
            checkState(!closed, "Solver manager was closed");
            final var solver = solverFactory.createItpSolver();
            instantiatedSolvers.add(solver);
            return solver;
        }
    }
}
