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
package hu.bme.mit.theta.solver.javasmt;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.UserPropagator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;
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
import org.sosy_lab.java_smt.solvers.yices2.PushPopYices2Prover;

public final class JavaSMTSolverFactory implements SolverFactory {
    private final Solvers solver;

    private final Configuration config;
    private final Configuration itpConfig;
    private final LogManager logger;

    /**
     * Available options (mined from javasmt sources): Prefix: solver Options: * private boolean
     * logAllQueries Export solver queries in SmtLib format into a file.
     * * @FileOption(FileOption.Type.OUTPUT_FILE) private @Nullable PathCounterTemplate logfile
     * Export solver queries in SmtLib format into a file. * private boolean
     * renameLogfileToAvoidConflicts If logging from the same application, avoid conflicting logfile
     * names. * private long randomSeed Random seed for SMT solver. * private Solvers solver Which
     * SMT solver to use. * private boolean useLogger Log solver actions, this may be slow! *
     * private boolean synchronize Sequentialize all solver actions to allow concurrent access! *
     * private boolean collectStatistics Counts all operations and interactions towards the SMT
     * solver. * private FloatingPointRoundingMode floatingPointRoundingMode Default rounding mode
     * for floating point operations. * private NonLinearArithmetic nonLinearArithmetic Use
     * non-linear arithmetic of the solver if supported and throw exception otherwise, Prefix:
     * solver.synchronized Options: * private boolean useSeperateProvers Use provers from a seperate
     * context to solve queries. Prefix: solver.boolector Options: * private SatSolver satSolver The
     * SAT solver used by Boolector. * private String furtherOptions Further options for Boolector
     * in addition to the default options. Prefix: solver.cvc5 Options: * private boolean
     * validateInterpolants apply additional validation checks for interpolation results Prefix:
     * solver.mathsat5 Options: * private String furtherOptions Further options that will be passed
     * to Mathsat in addition to the default options. * boolean loadOptimathsat5 Load less stable
     * optimizing version of mathsat5 solver. Prefix: solver.opensmt Options: * Logics logic
     * SMT-LIB2 name of the logic to be used by the solver. * int algBool Algorithm for boolean
     * interpolation * int algUf Algorithm for UF interpolation * int algLra Algorithm for LRA
     * interpolation Prefix: solver.princess Options: * private int minAtomsForAbbreviation The
     * number of atoms a term has to have before * private boolean enableAssertions Enable
     * additional assertion checks within Princess. * private boolean logAllQueriesAsScala log all
     * queries as Princess-specific Scala code * @FileOption(FileOption.Type.OUTPUT_FILE) private
     * PathCounterTemplate logAllQueriesAsScalaFile file for Princess-specific dump of queries as
     * Scala code Prefix: solver.smtinterpol Options: * private boolean checkResults Double check
     * generated results like interpolants and models whether they are correct * private
     * List<String> furtherOptions Further options that will be set to true for SMTInterpol Prefix:
     * solver.z3 Options: * private boolean usePhantomReferences Whether to use PhantomReferences
     * for discarding Z3 AST Prefix: solver.z3 Options: * boolean requireProofs Require proofs from
     * SMT solver * @FileOption(FileOption.Type.OUTPUT_FILE) @Nullable Path log Activate replayable
     * logging in Z3. * String optimizationEngine Engine to use for the optimization * String
     * objectivePrioritizationMode Ordering for objectives in the optimization context
     */
    private JavaSMTSolverFactory(
            Solvers solver, String[] args, Map<String, String> interpolationOptions) {
        try {
            this.solver = solver;
            final Configuration base = Configuration.fromCmdLineArguments(args);
            final var itpBuilder = Configuration.builder().copyFrom(base);
            interpolationOptions.forEach(itpBuilder::setOption);
            itpConfig = itpBuilder.build();
            // JavaSMT defaults Yices to MCSAT, the only backend that interpolates, but DPLL(T) is
            // far faster on difference logic.
            config =
                    Configuration.builder()
                            .copyFrom(base)
                            .setOption("solver.yices2.solverType", "dpllt")
                            .build();
            logger = BasicLogManager.create(config);
        } catch (InvalidConfigurationException e) {
            throw new JavaSMTSolverException(e);
        }
    }

    public static JavaSMTSolverFactory create(Solvers solver, Map<String, String> args) {
        return create(
                solver,
                args.entrySet().stream()
                        .flatMap(e -> Stream.of(e.getKey(), e.getValue()))
                        .toList());
    }

    public static JavaSMTSolverFactory create(Solvers solver, List<String> args) {
        return create(solver, args.toArray(new String[] {}));
    }

    public static JavaSMTSolverFactory create(Solvers solver, String[] args) {
        return new JavaSMTSolverFactory(solver, args, Map.of());
    }

    /**
     * {@code interpolationOptions} apply to the interpolating solvers only, and are set as they
     * are, so their values may contain {@code =}.
     */
    public static JavaSMTSolverFactory create(
            Solvers solver, String[] args, Map<String, String> interpolationOptions) {
        return new JavaSMTSolverFactory(solver, args, interpolationOptions);
    }

    @Override
    public Solver createSolver() {
        try {
            final ShutdownManager shutdown = ShutdownManager.create();
            final SolverContext context =
                    SolverContextFactory.createSolverContext(
                            config, logger, shutdown.getNotifier(), solver);
            final JavaSMTSymbolTable symbolTable = new JavaSMTSymbolTable();
            final JavaSMTTransformationManager transformationManager =
                    new JavaSMTTransformationManager(symbolTable, context);
            final JavaSMTTermTransformer termTransformer =
                    new JavaSMTTermTransformer(symbolTable, context);

            final ProverEnvironment prover = newProver(context, ProverOptions.GENERATE_MODELS);

            return new JavaSMTSolver(
                    symbolTable, transformationManager, termTransformer, context, prover, shutdown);
        } catch (InvalidConfigurationException e) {
            throw new JavaSMTSolverException(e);
        }
    }

    @Override
    public Solver createSolverWithPropagators(UserPropagator... propagators) {
        try {
            final ShutdownManager shutdown = ShutdownManager.create();
            final SolverContext context =
                    SolverContextFactory.createSolverContext(
                            config, logger, shutdown.getNotifier(), solver);
            final JavaSMTSymbolTable symbolTable = new JavaSMTSymbolTable();
            final JavaSMTTransformationManager transformationManager =
                    new JavaSMTTransformationManager(symbolTable, context);
            final JavaSMTTermTransformer termTransformer =
                    new JavaSMTTermTransformer(symbolTable, context);

            final ProverEnvironment prover =
                    context.newProverEnvironment(ProverOptions.GENERATE_MODELS);
            for (UserPropagator propagator : propagators) {
                final var adapter =
                        new JavaSMTUserPropagator(
                                propagator, transformationManager::toTerm, termTransformer::toExpr);
                if (!prover.registerUserPropagator(adapter)) {
                    throw new JavaSMTSolverException(
                            "Could not register user propagator " + propagator);
                }
                propagator.bind(adapter);
            }

            return new JavaSMTSolver(
                    symbolTable, transformationManager, termTransformer, context, prover, shutdown);
        } catch (InvalidConfigurationException e) {
            throw new JavaSMTSolverException(e);
        }
    }

    @Override
    public UCSolver createUCSolver() {
        try {
            final ShutdownManager shutdown = ShutdownManager.create();
            final SolverContext context =
                    SolverContextFactory.createSolverContext(
                            config, logger, shutdown.getNotifier(), solver);
            final JavaSMTSymbolTable symbolTable = new JavaSMTSymbolTable();
            final JavaSMTTransformationManager transformationManager =
                    new JavaSMTTransformationManager(symbolTable, context);
            final JavaSMTTermTransformer termTransformer =
                    new JavaSMTTermTransformer(symbolTable, context);

            final ProverEnvironment prover =
                    newProver(
                            context,
                            ProverOptions.GENERATE_MODELS,
                            ProverOptions.GENERATE_UNSAT_CORE);

            return new JavaSMTSolver(
                    symbolTable, transformationManager, termTransformer, context, prover, shutdown);
        } catch (InvalidConfigurationException e) {
            throw new JavaSMTSolverException(e);
        }
    }

    private ProverEnvironment newProver(SolverContext context, ProverOptions... options) {
        // Loading the Yices prover class loads the Yices native library, which some platforms lack.
        if (solver == Solvers.YICES2) {
            final ProverEnvironment yices = PushPopYices2Prover.create(context, Set.of(options));
            if (yices != null) {
                return yices;
            }
        }
        return context.newProverEnvironment(options);
    }

    @Override
    public ItpSolver createItpSolver() {
        try {
            final ShutdownManager shutdown = ShutdownManager.create();
            final SolverContext context =
                    SolverContextFactory.createSolverContext(
                            itpConfig, logger, shutdown.getNotifier(), solver);
            final JavaSMTSymbolTable symbolTable = new JavaSMTSymbolTable();
            final JavaSMTTransformationManager transformationManager =
                    new JavaSMTTransformationManager(symbolTable, context);
            final JavaSMTTermTransformer termTransformer =
                    new JavaSMTTermTransformer(symbolTable, context);

            final InterpolatingProverEnvironment prover =
                    context.newProverEnvironmentWithInterpolation(ProverOptions.GENERATE_MODELS);

            return new JavaSMTItpSolver(
                    symbolTable, transformationManager, termTransformer, context, prover, shutdown);
        } catch (InvalidConfigurationException e) {
            throw new JavaSMTSolverException(e);
        }
    }
}
