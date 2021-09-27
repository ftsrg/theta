package hu.bme.mit.theta.solver;

import java.util.ArrayList;
import java.util.Collection;

public abstract class SolverManager {
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

    public abstract boolean managesSolver(final String name);
    public abstract SolverFactory getSolverFactory(final String name) throws Exception;

}
