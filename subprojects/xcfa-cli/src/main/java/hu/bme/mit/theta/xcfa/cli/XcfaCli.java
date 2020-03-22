/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.cli;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarStatistics;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.common.table.BasicTableWriter;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.algorithm.PartialOrderExplicitChecker;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import hu.bme.mit.theta.xcfa.algorithm.ExplicitChecker;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.concurrent.TimeUnit;

public class XcfaCli {
    private static final String JAR_NAME = "theta-xcfa-cli.jar";
    private final String[] args;
    private final TableWriter writer;

    @Parameter(names = "--model", description = "Path of the input XCFA model", required = true)
    String model;

    @Parameter(names = "--loglevel", description = "Detailedness of logging")
    Logger.Level logLevel = Logger.Level.SUBSTEP;

    @Parameter(names = "--partialorder", description = "Use partial order reduction")
    Boolean partialOrder = false;

    @Parameter(names = "--benchmark", description = "Benchmark mode (only print metrics)")
    Boolean benchmarkMode = false;

    @Parameter(names = "--cex", description = "Log concrete counterexample")
    Boolean cexfile = false;

    @Parameter(names = "--header", description = "Print only a header (for benchmarks)", help = true)
    boolean headerOnly = false;

    private Logger logger;

    public XcfaCli(final String[] args) {
        this.args = args;
        writer = new BasicTableWriter(System.out, ",", "\"", "\"");
    }

    public static void main(final String[] args) {
        final XcfaCli mainApp = new XcfaCli(args);
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
            final XCFA xcfa = loadModel();

            final SafetyResult<?, ?> status;
            if (partialOrder) {
                final PartialOrderExplicitChecker checker = new PartialOrderExplicitChecker(xcfa);
                status = checker.check();
            } else {
                final ExplicitChecker checker = new ExplicitChecker(xcfa);
                status = checker.check();
            }
            sw.stop();
            printResult(status, xcfa, sw.elapsed(TimeUnit.MILLISECONDS));
            if (status.isUnsafe() && cexfile) {
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

    private XCFA loadModel() throws IOException {
        try (InputStream inputStream = new FileInputStream(model)) {
            return XcfaDslManager.createXcfa(inputStream);
        }
    }

    private void printResult(final SafetyResult<?, ?> status, final XCFA xcfa, final long totalTimeMs) {
        if (benchmarkMode) {
            final CegarStatistics stats = (CegarStatistics) status.getStats().get();
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
        logger.write(Logger.Level.RESULT, "%s", status.getTrace());
    }
}
