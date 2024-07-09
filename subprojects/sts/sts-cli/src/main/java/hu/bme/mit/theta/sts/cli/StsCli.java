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
package hu.bme.mit.theta.sts.cli;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarStatistics;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.common.CliUtils;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.common.table.BasicTableWriter;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.sts.STS;
import hu.bme.mit.theta.sts.StsUtils;
import hu.bme.mit.theta.sts.aiger.AigerParser;
import hu.bme.mit.theta.sts.aiger.AigerToSts;
import hu.bme.mit.theta.sts.aiger.elements.AigerSystem;
import hu.bme.mit.theta.sts.aiger.utils.AigerCoi;
import hu.bme.mit.theta.sts.analysis.StsAction;
import hu.bme.mit.theta.sts.analysis.StsTraceConcretizer;
import hu.bme.mit.theta.sts.analysis.config.StsConfig;
import hu.bme.mit.theta.sts.analysis.config.StsConfigBuilder;
import hu.bme.mit.theta.sts.analysis.config.StsConfigBuilder.Domain;
import hu.bme.mit.theta.sts.analysis.config.StsConfigBuilder.InitPrec;
import hu.bme.mit.theta.sts.analysis.config.StsConfigBuilder.PredSplit;
import hu.bme.mit.theta.sts.analysis.config.StsConfigBuilder.Refinement;
import hu.bme.mit.theta.sts.analysis.config.StsConfigBuilder.Search;
import hu.bme.mit.theta.sts.dsl.StsDslManager;
import hu.bme.mit.theta.sts.dsl.StsSpec;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.concurrent.TimeUnit;
import java.util.stream.Stream;

/**
 * A command line interface for running a CEGAR configuration on an STS.
 */
public class StsCli {

    private static final String JAR_NAME = "theta-sts-cli.jar";
    private final String[] args;
    private final TableWriter writer;

    enum Algorithm {
        CEGAR,
        KINDUCTION,
        IMC
    }

    @Parameter(names = {"--domain"}, description = "Abstract domain")
    Domain domain = Domain.PRED_CART;

    @Parameter(names = {"--algorithm"}, description = "Algorithm")
    Algorithm algorithm = Algorithm.CEGAR;

    @Parameter(names = {"--refinement"}, description = "Refinement strategy")
    Refinement refinement = Refinement.SEQ_ITP;

    @Parameter(names = {"--search"}, description = "Search strategy")
    Search search = Search.BFS;

    @Parameter(names = {"--predsplit"}, description = "Predicate splitting")
    PredSplit predSplit = PredSplit.WHOLE;

    @Parameter(names = {"--model"}, description = "Path of the input STS model", required = true)
    String model;

    @Parameter(names = {"--initprec"}, description = "Initial precision")
    InitPrec initPrec = InitPrec.EMPTY;

    @Parameter(names = "--prunestrategy", description = "Strategy for pruning the ARG after refinement")
    PruneStrategy pruneStrategy = PruneStrategy.LAZY;

    @Parameter(names = {"--loglevel"}, description = "Detailedness of logging")
    Logger.Level logLevel = Level.SUBSTEP;

    @Parameter(names = {"--benchmark"}, description = "Benchmark mode (only print metrics)")
    Boolean benchmarkMode = false;

    @Parameter(names = "--cex", description = "Write concrete counterexample to a file")
    String cexfile = null;

    @Parameter(names = {
            "--header"}, description = "Print only a header (for benchmarks)", help = true)
    boolean headerOnly = false;

    @Parameter(names = "--stacktrace", description = "Print full stack trace in case of exception")
    boolean stacktrace = false;

    @Parameter(names = "--version", description = "Display version", help = true)
    boolean versionInfo = false;

    private Logger logger;

    public StsCli(final String[] args) {
        this.args = args;
        writer = new BasicTableWriter(System.out, ",", "\"", "\"");
    }

    public static void main(final String[] args) {
        final StsCli mainApp = new StsCli(args);
        mainApp.run();
    }

    private void run() {
        try {
            JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(args);
            logger = benchmarkMode ? NullLogger.getInstance() : new ConsoleLogger(logLevel);
        } catch (final ParameterException ex) {
            System.out.println("Invalid parameters, details:");
            System.out.println(ex.getMessage());
            ex.usage();
            return;
        }

        if (headerOnly) {
            printHeader();
            return;
        }

        if (versionInfo) {
            CliUtils.printVersion(System.out);
            return;
        }

        try {
            final Stopwatch sw = Stopwatch.createStarted();
            final STS sts = loadModel();

            SafetyResult<? extends ARG<?, ?>, ? extends Trace<?, ?>> status = null;
            if (algorithm.equals(Algorithm.CEGAR)) {
                final StsConfig<?, ?, ?> configuration = buildConfiguration(sts);
                status = check(configuration);
            } else {
                throw new UnsupportedOperationException("Algorithm " + algorithm + " not supported");
            }
            sw.stop();
            printResult(status, sts, sw.elapsed(TimeUnit.MILLISECONDS));
            if (status.isUnsafe() && cexfile != null) {
                writeCex(sts, status.asUnsafe());
            }
        } catch (final Throwable ex) {
            printError(ex);
            System.exit(1);
        }
    }

    private SafetyResult<? extends ARG<?, ?>, ? extends Trace<?, ?>> check(StsConfig<?, ?, ?> configuration) throws Exception {
        try {
            return configuration.check();
        } catch (final Exception ex) {
            String message = ex.getMessage() == null ? "(no message)" : ex.getMessage();
            throw new Exception(
                    "Error while running algorithm: " + ex.getClass().getSimpleName() + " " + message,
                    ex);
        }
    }

    private void printHeader() {
        Stream.of("Result", "TimeMs", "AlgoTimeMs", "AbsTimeMs", "RefTimeMs", "Iterations",
                        "ArgSize", "ArgDepth", "ArgMeanBranchFactor", "CexLen", "Vars", "Size")
                .forEach(writer::cell);
        writer.newRow();
    }

    private STS loadModel() throws Exception {
        try {
            if (model.endsWith(".aag")) {
                final AigerSystem aigerSystem = AigerParser.parse(model);
                AigerCoi.apply(aigerSystem);
                return AigerToSts.createSts(aigerSystem);
            } else {
                try (InputStream inputStream = new FileInputStream(model)) {
                    final StsSpec spec = StsDslManager.createStsSpec(inputStream);
                    if (spec.getAllSts().size() != 1) {
                        throw new UnsupportedOperationException(
                                "STS contains multiple properties.");
                    }
                    return StsUtils.eliminateIte(Utils.singleElementOf(spec.getAllSts()));
                }
            }
        } catch (Exception ex) {
            throw new Exception("Could not parse STS: " + ex.getMessage(), ex);
        }
    }

    private StsConfig<?, ?, ?> buildConfiguration(final STS sts) throws Exception {
        try {
            return new StsConfigBuilder(domain, refinement, Z3LegacySolverFactory.getInstance())
                    .initPrec(initPrec).search(search)
                    .predSplit(predSplit).pruneStrategy(pruneStrategy).logger(logger).build(sts);
        } catch (final Exception ex) {
            throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
        }
    }

    private void printResult(final SafetyResult<? extends ARG<?, ?>, ? extends Trace<?, ?>> status, final STS sts,
                             final long totalTimeMs) {
        final CegarStatistics stats = (CegarStatistics) status.getStats().get();
        if (benchmarkMode) {
            writer.cell(status.isSafe());
            writer.cell(totalTimeMs);
            writer.cell(stats.getAlgorithmTimeMs());
            writer.cell(stats.getAbstractorTimeMs());
            writer.cell(stats.getRefinerTimeMs());
            writer.cell(stats.getIterations());
            writer.cell(status.getWitness().size());
            writer.cell(status.getWitness().getDepth());
            writer.cell(status.getWitness().getMeanBranchingFactor());
            if (status.isUnsafe()) {
                writer.cell(status.asUnsafe().getCex().length() + "");
            } else {
                writer.cell("");
            }
            writer.cell(sts.getVars().size());
            writer.cell(ExprUtils.nodeCountSize(BoolExprs.And(sts.getInit(), sts.getTrans())));
            writer.newRow();
        }
    }

    private void printError(final Throwable ex) {
        final String message = ex.getMessage() == null ? "" : ex.getMessage();
        if (benchmarkMode) {
            writer.cell("[EX] " + ex.getClass().getSimpleName() + ": " + message);
            writer.newRow();
        } else {
            logger.write(Level.RESULT, "%s occurred, message: %s%n", ex.getClass().getSimpleName(),
                    message);
            if (stacktrace) {
                final StringWriter errors = new StringWriter();
                ex.printStackTrace(new PrintWriter(errors));
                logger.write(Level.RESULT, "Trace:%n%s%n", errors.toString());
            } else {
                logger.write(Level.RESULT, "Use --stacktrace for stack trace%n");
            }
        }
    }

    private void writeCex(final STS sts, final SafetyResult.Unsafe<?, ? extends Trace<?, ?>> status)
            throws FileNotFoundException {
        @SuppressWarnings("unchecked") final Trace<ExprState, StsAction> trace = (Trace<ExprState, StsAction>) status.getCex();
        final Trace<Valuation, StsAction> concrTrace = StsTraceConcretizer.concretize(sts, trace,
                Z3LegacySolverFactory.getInstance());
        final File file = new File(cexfile);
        PrintWriter printWriter = null;
        try {
            printWriter = new PrintWriter(file);
            for (Valuation state : concrTrace.getStates()) {
                printWriter.println(state.toString());
            }
        } finally {
            if (printWriter != null) {
                printWriter.close();
            }
        }
    }
}
