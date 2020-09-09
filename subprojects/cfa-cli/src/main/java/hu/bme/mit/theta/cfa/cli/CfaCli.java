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
package hu.bme.mit.theta.cfa.cli;

import java.io.*;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Stream;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Stopwatch;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult.Unsafe;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarStatistics;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.cfa.analysis.CfaTraceConcretizer;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfig;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Domain;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Encoding;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.InitPrec;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.PrecGranularity;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.PredSplit;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Refinement;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Search;
import hu.bme.mit.theta.cfa.analysis.utils.CfaVisualizer;
import hu.bme.mit.theta.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.common.table.BasicTableWriter;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.*;
import hu.bme.mit.theta.solver.z3.*;

/**
 * A command line interface for running a CEGAR configuration on a CFA.
 */
public class CfaCli {
	private static final String JAR_NAME = "theta-cfa-cli.jar";
	private final SolverFactory solverFactory = Z3SolverFactory.getInstance();
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
	Integer maxEnum = 10;

	@Parameter(names = "--initprec", description = "Initial precision of abstraction")
	InitPrec initPrec = InitPrec.EMPTY;

	@Parameter(names = "--prunestrategy", description = "Strategy for pruning the ARG after refinement")
	PruneStrategy pruneStrategy = PruneStrategy.LAZY;

	@Parameter(names = "--loglevel", description = "Detailedness of logging")
	Logger.Level logLevel = Level.SUBSTEP;

	@Parameter(names = "--benchmark", description = "Benchmark mode (only print metrics)")
	Boolean benchmarkMode = false;

	@Parameter(names = "--cex", description = "Write concrete counterexample to a file")
	String cexfile = null;

	@Parameter(names = "--header", description = "Print only a header (for benchmarks)", help = true)
	boolean headerOnly = false;

	@Parameter(names = "--visualize", description = "Visualize CFA to this file without running the algorithm")
	String visualize = null;

	@Parameter(names = "--metrics", description = "Print metrics about the CFA without running the algorithm")
	boolean metrics = false;

	@Parameter(names = "--stacktrace", description = "Print full stack trace in case of exception")
	boolean stacktrace = false;

	private Logger logger;

	public CfaCli(final String[] args) {
		this.args = args;
		writer = new BasicTableWriter(System.out, ",", "\"", "\"");
	}

	public static void main(final String[] args) {
		final CfaCli mainApp = new CfaCli(args);
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
			final CFA cfa = loadModel();

			if (visualize != null) {
				final Graph graph = CfaVisualizer.visualize(cfa);
				GraphvizWriter.getInstance().writeFileAutoConvert(graph, visualize);
				return;
			}

			if (metrics) {
				CfaMetrics.printMetrics(logger, cfa);
				return;
			}

			final CfaConfig<?, ?, ?> configuration = buildConfiguration(cfa);
			final SafetyResult<?, ?> status = check(configuration);
			sw.stop();
			printResult(status, sw.elapsed(TimeUnit.MILLISECONDS));
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
		Stream.of("Result", "TimeMs", "AlgoTimeMs", "AbsTimeMs", "RefTimeMs", "Iterations",
				"ArgSize", "ArgDepth", "ArgMeanBranchFactor", "CexLen").forEach(writer::cell);
		writer.newRow();
	}

	private CFA loadModel() throws Exception {
		try (InputStream inputStream = new FileInputStream(model)) {
			try {
				return CfaDslManager.createCfa(inputStream);
			} catch (final Exception ex) {
				throw new Exception("Could not parse CFA: " + ex.getMessage(), ex);
			}
		}
	}

	private CfaConfig<?, ?, ?> buildConfiguration(final CFA cfa) throws Exception {
		try {
			return new CfaConfigBuilder(domain, refinement, solverFactory).precGranularity(precGranularity).search(search)
					.predSplit(predSplit).encoding(encoding).maxEnum(maxEnum).initPrec(initPrec)
					.pruneStrategy(pruneStrategy).logger(logger).build(cfa);
		} catch (final Exception ex) {
			throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
		}
	}

	private SafetyResult<?, ?> check(CfaConfig<?, ?, ?> configuration) throws Exception {
		try {
			return configuration.check();
		} catch (final Exception ex) {
			throw new Exception("Error while running algorithm: " + ex.getMessage(), ex);
		}
	}

	private void printResult(final SafetyResult<?, ?> status, final long totalTimeMs) {
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
		final String message = ex.getMessage() == null ? "" : ex.getMessage();
		if (benchmarkMode) {
			writer.cell("[EX] " + ex.getClass().getSimpleName() + ": " + message);
		} else {
			logger.write(Level.RESULT, "%s occurred, message: %s%n", ex.getClass().getSimpleName(), message);
			if (stacktrace) {
				final StringWriter errors = new StringWriter();
				ex.printStackTrace(new PrintWriter(errors));
				logger.write(Level.RESULT, "Trace:%n%s%n", errors.toString());
			} else {
				logger.write(Level.RESULT, "Use --stacktrace for stack trace%n");
			}
		}
	}

	private void writeCex(final Unsafe<?, ?> status) {
		@SuppressWarnings("unchecked") final Trace<CfaState<?>, CfaAction> trace = (Trace<CfaState<?>, CfaAction>) status.getTrace();
		final Trace<CfaState<ExplState>, CfaAction> concrTrace = CfaTraceConcretizer.concretize(trace, solverFactory);
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
