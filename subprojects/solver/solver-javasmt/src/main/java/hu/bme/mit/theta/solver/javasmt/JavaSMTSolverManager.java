/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.javasmt;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverBase;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.UCSolver;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

import java.util.HashSet;
import java.util.Set;
import java.util.regex.Pattern;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public final class JavaSMTSolverManager extends SolverManager {

    private static final Pattern NAME_PATTERN = Pattern.compile("JavaSMT:(.*)");

    private boolean closed = false;
    private final Set<SolverBase> instantiatedSolvers = new HashSet<>();

    private JavaSMTSolverManager() {
    }

    public static JavaSMTSolverManager create() {
        return new JavaSMTSolverManager();
    }

    @Override
    public boolean managesSolver(final String name) {
        return NAME_PATTERN.matcher(name).matches();
    }

    @Override
    public SolverFactory getSolverFactory(final String name) throws InvalidConfigurationException {
        final var matcher = NAME_PATTERN.matcher(name);
        checkArgument(matcher.matches());
        final var solverName = matcher.group(1);
        final var solver = Solvers.valueOf(solverName);

        return new ManagedFactory(JavaSMTSolverFactory.create(solver, new String[]{"--nonLinearArithmetic=USE"}));
    }

    @Override
    public synchronized void close() throws Exception {
        for (final var solver : instantiatedSolvers) {
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
