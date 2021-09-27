package hu.bme.mit.theta.solver;

import java.util.ArrayList;
import java.util.Collection;

/**
 * Owns the lifecycle of the Solvers created by the SolverFactory instances returned by resolveSolverFactory
 */
public abstract class SolverManager implements AutoCloseable {
    private static final Collection<SolverManager> solverManagers = new ArrayList<>();

    public static void registerSolverManager(final SolverManager solverManager) {
        solverManagers.add(solverManager);
    }

    public static SolverFactory resolveSolverFactory(final String name) throws Exception {
        for(final SolverManager solverManager : solverManagers) {
            if(solverManager.managesSolver(name)) {
                return solverManager.getSolverFactory(name);
            }
        }

        throw new UnsupportedOperationException("Solver " + name + " not supported");
    }

    /**
     * Closes all SolverManager instances registered
     */
    public static void closeAll() throws Exception {
        for(final var solverManager : solverManagers) {
            solverManager.close();
        }
        solverManagers.clear();
    }

    public abstract boolean managesSolver(final String name);
    public abstract SolverFactory getSolverFactory(final String name) throws Exception;

}
