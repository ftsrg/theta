package hu.bme.mit.theta.xsts.cli;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.*;
import hu.bme.mit.theta.analysis.algorithm.cegar.*;
import hu.bme.mit.theta.analysis.expl.*;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.common.table.BasicTableWriter;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xsts.analysis.*;


import java.io.*;
import java.util.concurrent.TimeUnit;

public class XstsCli {

    private static final String JAR_NAME = "theta-xsts-cli.jar";
    private final SolverFactory solverFactory = Z3SolverFactory.getInstace();
    private final String[] args;
    private final TableWriter writer;

    @Parameter(names = "--domain", description = "Abstract domain")
    Domain domain = Domain.PRED_CART;

    @Parameter(names = "--refinement", description = "Refinement strategy")
    Refinement refinement = Refinement.SEQ_ITP;

    @Parameter(names = "--search", description = "Search strategy")
    Search search = Search.BFS;

    @Parameter(names = "--predsplit", description = "Predicate splitting (for predicate abstraction)")
    PredSplit predSplit = PredSplit.WHOLE;

    @Parameter(names = "--model", description = "Path of the input CFA model", required = true)
    String model;

    @Parameter(names = "--precgranularity", description = "Precision granularity")
    PrecGranularity precGranularity = PrecGranularity.GLOBAL;

    @Parameter(names = "--encoding", description = "Block encoding")
    Encoding encoding = Encoding.LBE;

    @Parameter(names = "--maxenum", description = "Maximal number of explicitly enumerated successors (0: unlimited)")
    Integer maxEnum = 0;

    @Parameter(names = "--initprec", description = "Initial precision of abstraction")
    InitPrec initPrec = InitPrec.EMPTY;

    @Parameter(names = "--loglevel", description = "Detailedness of logging")
    Logger.Level logLevel = Logger.Level.SUBSTEP;

    @Parameter(names = "--benchmark", description = "Benchmark mode (only print metrics)")
    Boolean benchmarkMode = false;

    @Parameter(names = "--cex", description = "Write concrete counterexample to a file")
    String cexfile = null;

    @Parameter(names = "--header", description = "Print only a header (for benchmarks)", help = true)
    boolean headerOnly = false;

    private Logger logger;

    public XstsCli(final String[] args) {
        this.args = args;
        writer = new BasicTableWriter(System.out, ",", "\"", "\"");
    }

    public static void main(final String[] args) {
        final XstsCli mainApp = new XstsCli(args);
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

        try {
            final Stopwatch sw = Stopwatch.createStarted();
            final CFA xsts = loadModel();
            final XstsConfig<?, ?, ?> configuration = buildConfiguration(xsts);
            final SafetyResult<?, ?> status = configuration.check();
            sw.stop();
            printResult(status, xsts, sw.elapsed(TimeUnit.MILLISECONDS));
            if (status.isUnsafe() && cexfile != null) {
                writeCex(status.asUnsafe());
            }
        } catch (final Throwable ex) {
            printError(ex);
        }
        if (benchmarkMode) {
            writer.newRow();
        }
    }

    private void printHeader() {
        final String[] header = new String[]{"Result", "TimeMs", "AlgoTimeMs", "AbsTimeMs", "RefTimeMs", "Iterations",
                "ArgSize", "ArgDepth", "ArgMeanBranchFactor", "CexLen"};
        for (final String str : header) {
            writer.cell(str);
        }
        writer.newRow();
    }

    private CFA loadModel() throws IOException {
        try (InputStream inputStream = new FileInputStream(model)) {
            final CFA xsts = XstsDslManager.createXsts(inputStream);
            return xsts;
        }
    }

    private XstsConfig<?, ?, ?> buildConfiguration(final CFA xsts) {
        return new XstsConfigBuilder(domain, refinement, solverFactory).precGranularity(precGranularity).search(search)
                .predSplit(predSplit).encoding(encoding).maxEnum(maxEnum).initPrec(initPrec).logger(logger).build(xsts);
    }

    private void printResult(final SafetyResult<?, ?> status, final CFA xsts, final long totalTimeMs) {
        final CegarStatistics stats = (CegarStatistics) status.getStats().get();
        if (benchmarkMode) {
            writer.cell(status.isSafe());
            writer.cell(totalTimeMs);
            writer.cell(stats.getAlgorithmTimeMs());
            writer.cell(stats.getAbstractorTimeMs());
            writer.cell(stats.getRefinerTimeMs());
            writer.cell(stats.getIterations());
            writer.cell(status.getArg().size());
            writer.cell(status.getArg().getDepth());
            writer.cell(status.getArg().getMeanBranchingFactor());
            if (status.isUnsafe()) {
                writer.cell(status.asUnsafe().getTrace().length() + "");
            } else {
                writer.cell("");
            }
        }
    }

    private void printError(final Throwable ex) {
        final String message = ex.getMessage() == null ? "" : ": " + ex.getMessage();
        if (benchmarkMode) {
            writer.cell("[EX] " + ex.getClass().getSimpleName() + message);
        } else {
            logger.write(Logger.Level.RESULT, "Exception of type %s occurred%n", ex.getClass().getSimpleName());
            logger.write(Logger.Level.MAINSTEP, "Message:%n%s%n", ex.getMessage());
            final StringWriter errors = new StringWriter();
            ex.printStackTrace(new PrintWriter(errors));
            logger.write(Logger.Level.SUBSTEP, "Trace:%n%s%n", errors.toString());
        }
    }

    private void writeCex(final SafetyResult.Unsafe<?, ?> status) {
        @SuppressWarnings("unchecked") final Trace<XstsState<?>, XstsAction> trace = (Trace<XstsState<?>, XstsAction>) status.getTrace();
        final Trace<XstsState<ExplState>, XstsAction> concrTrace = XstsTraceConcretizer.concretize(trace, solverFactory);
        final File file = new File(cexfile);
        PrintWriter printWriter = null;
        try {
            printWriter = new PrintWriter(file);
            printWriter.write(concrTrace.toString());
        } catch (final FileNotFoundException e) {
            printError(e);
        } finally {
            if (printWriter != null) {
                printWriter.close();
            }
        }
    }

}
