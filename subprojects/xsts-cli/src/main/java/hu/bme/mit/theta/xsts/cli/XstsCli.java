package hu.bme.mit.theta.xsts.cli;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.*;
import hu.bme.mit.theta.analysis.algorithm.cegar.*;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.utils.TraceVisualizer;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.common.table.BasicTableWriter;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.XstsAction;
import hu.bme.mit.theta.xsts.analysis.XstsState;
import hu.bme.mit.theta.xsts.analysis.concretizer.XstsStateSequence;
import hu.bme.mit.theta.xsts.analysis.concretizer.XstsTraceConcretizer;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfig;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.Domain;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.Refinement;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.InitPrec;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.PredSplit;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.Search;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;

import java.io.*;
import java.util.concurrent.TimeUnit;

public class XstsCli {

    private static final String JAR_NAME = "theta-xsts-cli.jar";
    private final SolverFactory solverFactory = Z3SolverFactory.getInstace();
    private final String[] args;
    private final TableWriter writer;

    @Parameter(names = {"--domain"}, description = "Abstract domain")
    Domain domain = Domain.PRED_CART;

    @Parameter(names = {"--refinement"}, description = "Refinement strategy")
    Refinement refinement = Refinement.SEQ_ITP;

    @Parameter(names = {"--search"}, description = "Search strategy")
    Search search = Search.BFS;

    @Parameter(names = {"--predsplit"}, description = "Predicate splitting")
    PredSplit predSplit = PredSplit.WHOLE;

    @Parameter(names = {"--model"}, description = "Path of the input XSTS model", required = true)
    String model;

    @Parameter(names = {"--property"}, description = "Path of the input property", required = true)
    String property;

    @Parameter(names = {"--initprec"}, description = "Initial precision")
    InitPrec initPrec = InitPrec.EMPTY;

    @Parameter(names = {"--loglevel"}, description = "Detailedness of logging")
    Logger.Level logLevel = Logger.Level.SUBSTEP;

    @Parameter(names = {"--benchmark"}, description = "Benchmark mode (only print metrics)")
    Boolean benchmarkMode = false;

    @Parameter(names = {"--visualize"}, description = "Write proof or counterexample to file in dot format")
    String dotfile = null;

    @Parameter(names = {"--cex"}, description = "Write concrete counterexample to a file")
    String cexfile = null;

    @Parameter(names = {"--header"}, description = "Print only a header (for benchmarks)", help = true)
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
            final XSTS xsts = loadModel();
            final XstsConfig<?, ?, ?> configuration = buildConfiguration(xsts);
            final SafetyResult<?, ?> status = configuration.check();
            sw.stop();
            printResult(status, xsts, sw.elapsed(TimeUnit.MILLISECONDS));
            if (status.isUnsafe() && cexfile != null) {
                writeCex(status.asUnsafe(),xsts);
            }
            if (dotfile != null) {
                writeVisualStatus(status, dotfile);
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
                "ArgSize", "ArgDepth", "ArgMeanBranchFactor", "CexLen", "Vars"};
        for (final String str : header) {
            writer.cell(str);
        }
        writer.newRow();
    }

    private XSTS loadModel() throws IOException {
        if (model.endsWith(".xsts") && property.endsWith(".prop")) {
            try (SequenceInputStream inputStream = new SequenceInputStream(new FileInputStream(model),new FileInputStream(property))) {
                return XstsDslManager.createXsts(inputStream);
            }
        } else {
            throw new IOException("Unknown format");
        }
    }

    private XstsConfig<?, ?, ?> buildConfiguration(final XSTS xsts) {
        return new XstsConfigBuilder(domain, refinement, solverFactory).initPrec(initPrec).search(search)
                .predSplit(predSplit).logger(logger).build(xsts);
    }

    private void printResult(final SafetyResult<?, ?> status, final XSTS sts, final long totalTimeMs) {
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
            writer.cell(sts.getVars().size());
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

    private void writeVisualStatus(final SafetyResult<?, ?> status, final String filename)
            throws FileNotFoundException {
        final Graph graph = status.isSafe()
                ? new ArgVisualizer<>(State::toString, a -> "").visualize(status.asSafe().getArg())
                : new TraceVisualizer<>(State::toString, a -> "").visualize(status.asUnsafe().getTrace());
        GraphvizWriter.getInstance().writeFile(graph, filename);
    }

    private void writeCex(final SafetyResult.Unsafe<?, ?> status, final XSTS xsts) {
        //TODO remove temp vars, replace int values with literals

        @SuppressWarnings("unchecked") final Trace<XstsState<?>, XstsAction> trace = (Trace<XstsState<?>, XstsAction>) status.getTrace();
        final XstsStateSequence concrTrace = XstsTraceConcretizer.concretize(trace, solverFactory, xsts);
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
