/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.solver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.Callable;

/**
 * Owns the lifecycle of the Solvers created by the SolverFactory instances returned by
 * resolveSolverFactory
 */
public abstract class SolverManager implements AutoCloseable {

    private static final Collection<SolverManager> solverManagers = new ArrayList<>();

    public static void registerSolverManager(final SolverManager solverManager) {
        solverManagers.add(solverManager);
    }

    public static SolverFactory resolveSolverFactory(final String name) throws Exception {
        for (final SolverManager solverManager : solverManagers) {
            if (solverManager.managesSolver(name)) {
                return solverManager.getSolverFactory(name);
            }
        }

        throw new UnsupportedOperationException("Solver " + name + " not supported");
    }

    /** Closes all SolverManager instances registered */
    public static void closeAll() throws Exception {
        for (final var solverManager : solverManagers) {
            solverManager.close();
        }
        solverManagers.clear();
    }

    private static final ThreadLocal<List<SolverBase>> solverScope = new ThreadLocal<>();

    /**
     * Runs {@code action} in a solver scope: solvers that managed factories create on this thread
     * meanwhile are closed when it finishes, not kept until {@link #closeAll()}.
     */
    public static <T> T withSolverScope(final Callable<T> action) throws Exception {
        return withSolverScope(new Object(), action);
    }

    /**
     * Like {@link #withSolverScope(Callable)}, but closes solvers while holding {@code closeLock}
     * (for libraries whose native contexts must not be created and destroyed concurrently).
     */
    public static <T> T withSolverScope(final Object closeLock, final Callable<T> action)
            throws Exception {
        final List<SolverBase> outer = solverScope.get();
        final List<SolverBase> scope = new ArrayList<>();
        solverScope.set(scope);
        try {
            return action.call();
        } finally {
            solverScope.set(outer);
            synchronized (closeLock) {
                for (final SolverBase solver : scope) {
                    solver.close();
                }
            }
        }
    }

    /**
     * Hands {@code solver} to the current thread's solver scope, if any; returns whether it took
     * ownership (otherwise the manager keeps tracking the solver).
     */
    protected static boolean adoptIntoSolverScope(final SolverBase solver) {
        final List<SolverBase> scope = solverScope.get();
        if (scope == null) {
            return false;
        }
        scope.add(solver);
        return true;
    }

    public abstract boolean managesSolver(final String name);

    public abstract SolverFactory getSolverFactory(final String name) throws Exception;
}
