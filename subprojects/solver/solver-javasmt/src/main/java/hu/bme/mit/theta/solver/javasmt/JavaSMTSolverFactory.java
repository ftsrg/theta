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
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

public final class JavaSMTSolverFactory implements SolverFactory {
    private final Solvers solver;

    private final Configuration config;
    private final LogManager logger;
    private final ShutdownManager shutdownManager;

    private JavaSMTSolverFactory(Solvers solver, String[] args) {
        try {
            this.solver = solver;
            config = Configuration.fromCmdLineArguments(args);
            logger = BasicLogManager.create(config);
            shutdownManager = ShutdownManager.create();
        } catch (InvalidConfigurationException e) {
            throw new JavaSMTSolverException(e);
        }
    }
    public static JavaSMTSolverFactory create(Solvers solver, Map<String, String> args) {
        return create(solver, args.entrySet().stream().flatMap(e -> Stream.of(e.getKey(), e.getValue())).toList());
    }
    public static JavaSMTSolverFactory create(Solvers solver, List<String> args)  {
        return create(solver, args.toArray(new String[]{}));
    }

    public static JavaSMTSolverFactory create(Solvers solver, String[] args) {
        return new JavaSMTSolverFactory(solver, args);
    }

    @Override
    public Solver createSolver() {
        try {
            final SolverContext context = SolverContextFactory.createSolverContext(config, logger, shutdownManager.getNotifier(), solver);
            final JavaSMTSymbolTable symbolTable = new JavaSMTSymbolTable();
            final JavaSMTTransformationManager transformationManager = new JavaSMTTransformationManager(symbolTable, context);
            final JavaSMTTermTransformer termTransformer = new JavaSMTTermTransformer(symbolTable, context);

            final ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS);

            return new JavaSMTSolver(symbolTable, transformationManager, termTransformer, context, prover);
        } catch (InvalidConfigurationException e) {
            throw new JavaSMTSolverException(e);
        }
    }

    @Override
    public UCSolver createUCSolver() {
        try {
            final SolverContext context = SolverContextFactory.createSolverContext(config, logger, shutdownManager.getNotifier(), solver);
            final JavaSMTSymbolTable symbolTable = new JavaSMTSymbolTable();
            final JavaSMTTransformationManager transformationManager = new JavaSMTTransformationManager(symbolTable, context);
            final JavaSMTTermTransformer termTransformer = new JavaSMTTermTransformer(symbolTable, context);

            final ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS, ProverOptions.GENERATE_UNSAT_CORE);

            return new JavaSMTSolver(symbolTable, transformationManager, termTransformer, context, prover);
        } catch (InvalidConfigurationException e) {
            throw new JavaSMTSolverException(e);
        }
    }

    @Override
    public ItpSolver createItpSolver() {
        try {
            final SolverContext context = SolverContextFactory.createSolverContext(config, logger, shutdownManager.getNotifier(), solver);
            final JavaSMTSymbolTable symbolTable = new JavaSMTSymbolTable();
            final JavaSMTTransformationManager transformationManager = new JavaSMTTransformationManager(symbolTable, context);
            final JavaSMTTermTransformer termTransformer = new JavaSMTTermTransformer(symbolTable, context);

            final InterpolatingProverEnvironment prover = context.newProverEnvironmentWithInterpolation(ProverOptions.GENERATE_MODELS);

            return new JavaSMTItpSolver(symbolTable, transformationManager, termTransformer, context, prover);
        } catch (InvalidConfigurationException e) {
            throw new JavaSMTSolverException(e);
        }
    }

}
