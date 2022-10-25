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
package hu.bme.mit.theta.xta.cli;

import java.io.*;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expr.ExprMeetStrategy;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.utils.TraceVisualizer;
import hu.bme.mit.theta.common.CliUtils;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.common.table.BasicTableWriter;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.combinedlazycegar.CombinedLazyCegarXtaCheckerConfigFactory;
import hu.bme.mit.theta.xta.analysis.lazy.*;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import hu.bme.mit.theta.xta.utils.CTLOperatorNotSupportedException;
import hu.bme.mit.theta.xta.utils.MixedDataTimeNotSupportedException;

public final class XtaCli {

	public enum Algorithm {
		LAZY, EXPERIMENTAL_EAGERLAZY
	}

	private static final String JAR_NAME = "theta-xta.jar";
	private final String[] args;
	private final TableWriter writer;

	@Parameter(names = {"--model", "-m"}, description = "Path of the input model", required = true)
	String model;

	@Parameter(names = {"--discreteconcr", "-dc"}, description = "Concrete domain for discrete variables", required = false)
	DataStrategy2.ConcrDom concrDataDom = DataStrategy2.ConcrDom.EXPL;

	@Parameter(names = {"--discreteabstr", "-da"}, description = "Abstract domain for discrete variables", required = false)
	DataStrategy2.AbstrDom abstrDataDom = DataStrategy2.AbstrDom.EXPL;

	@Parameter(names = {"--discreteitp", "-di"}, description = "Interpolation strategy for discrete variables", required = false)
	DataStrategy2.ItpStrategy dataItpStrategy = DataStrategy2.ItpStrategy.BIN_BW;

	@Parameter(names = {"--meet", "-me"}, description = "Meet strategy for expressions", required = false)
	ExprMeetStrategy exprMeetStrategy = ExprMeetStrategy.BASIC;

	@Parameter(names = {"--clock", "-c"}, description = "Refinement strategy for clock variables", required = false)
	ClockStrategy clockStrategy = ClockStrategy.BWITP;

	@Parameter(names = {"--search", "-s"}, description = "Search strategy", required = false)
	SearchStrategy searchStrategy = SearchStrategy.BFS;

	@Parameter(names = {"--benchmark", "-b"}, description = "Benchmark mode (only print metrics)")
	Boolean benchmarkMode = false;

	@Parameter(names = {"--visualize", "-v"}, description = "Write proof or counterexample to file in dot format")
	String dotfile = null;

	@Parameter(names = {"--header", "-h"}, description = "Print only a header (for benchmarks)", help = true)
	boolean headerOnly = false;

	@Parameter(names = "--stacktrace", description = "Print full stack trace in case of exception")
	boolean stacktrace = false;

	@Parameter(names = "--loglevel", description = "Detailedness of logging")
	Logger.Level logLevel = Logger.Level.MAINSTEP;

	@Parameter(names = "--version", description = "Display version", help = true)
	boolean versionInfo = false;

	@Parameter(names = {"--algorithm"}, description = "The algorithm to use")
	Algorithm algorithm = Algorithm.LAZY;

	public XtaCli(final String[] args) {
		this.args = args;
		this.writer = new BasicTableWriter(System.out, ",", "\"", "\"");
	}

	public static void main(final String[] args) {
		final XtaCli mainApp = new XtaCli(args);
		mainApp.run();
	}

	private void run() {
		try {
			JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(args);
		} catch (final ParameterException ex) {
			System.out.println("Invalid parameters, details:");
			System.out.println(ex.getMessage());
			ex.usage();
			return;
		}

		if (headerOnly) {
			LazyXtaStatistics.writeHeader(writer);
			return;
		}

		if (versionInfo) {
			CliUtils.printVersion(System.out);
			return;
		}

		try {
			final XtaSystem system = loadModel();
			switch (algorithm) {
				case LAZY -> runLazy(system);
				case EXPERIMENTAL_EAGERLAZY -> runCombined(system);
			}
		} catch (final Throwable ex) {
			printError(ex);
			System.exit(1);
		}
	}

	private void runLazy(final XtaSystem system) {
		final LazyXtaAbstractorConfig<?, ?, ?> abstractor = LazyXtaAbstractorConfigFactory.create(
			system, new DataStrategy2(concrDataDom, abstrDataDom, dataItpStrategy),
			clockStrategy, searchStrategy, exprMeetStrategy
		);
		final var result = abstractor.check();
		resultPrinter(result.isSafe(), result.isUnsafe(), system);
	}

	private void runCombined(final XtaSystem system) {
		final var config = CombinedLazyCegarXtaCheckerConfigFactory.create(system, NullLogger.getInstance(), Z3SolverFactory.getInstance()).build();
		final var result = config.check();
		resultPrinter(result.isSafe(), result.isUnsafe(), system);
	}

	private void resultPrinter(final boolean isSafe, final boolean isUnsafe, final XtaSystem system) {
		if (isSafe) {
			switch (system.getPropertyKind()) {
				case AG -> System.out.println("(SafetyResult Safe)");
				case EF -> System.out.println("(SafetyResult Unsafe)");
				default -> throw new UnsupportedOperationException();
			}
		} else if (isUnsafe) {
			switch (system.getPropertyKind()) {
				case AG -> System.out.println("(SafetyResult Unsafe)");
				case EF -> System.out.println("(SafetyResult Safe)");
				default -> throw new UnsupportedOperationException();
			}
		} else {
			throw new UnsupportedOperationException();
		}
	}

	private SafetyResult<?, ?> check(SafetyChecker<?, ?, UnitPrec> checker) throws Exception {
		try {
			return checker.check(UnitPrec.getInstance());
		} catch (final Exception ex) {
			String message = ex.getMessage() == null ? "(no message)" : ex.getMessage();
			throw new Exception("Error while running algorithm: " + ex.getClass().getSimpleName() + " " + message, ex);
		}
	}

	private XtaSystem loadModel() throws Exception {
		try {
			try (InputStream inputStream = new FileInputStream(model)) {
				return XtaDslManager.createSystem(inputStream);
			}
		} catch (CTLOperatorNotSupportedException ex) {
			ex.printStackTrace();
			System.exit(11);
		} catch (MixedDataTimeNotSupportedException ex) {
			ex.printStackTrace();
			System.exit(12);
		} catch (Exception ex) {
			ex.printStackTrace();
			System.exit(10);
		}
		throw new AssertionError();
	}

	private void printResult(final SafetyResult<?, ?> result) {
		final LazyXtaStatistics stats = (LazyXtaStatistics) result.getStats().get();
		if (benchmarkMode) {
			stats.writeData(writer);
		} else {
			System.out.println(stats.toString());
		}
	}

	private void printError(final Throwable ex) {
		final String message = ex.getMessage() == null ? "" : ": " + ex.getMessage();
		if (benchmarkMode) {
			writer.cell("[EX] " + ex.getClass().getSimpleName() + message);
		} else {
			System.out.println(ex.getClass().getSimpleName() + " occurred, message: " + message);
			if (stacktrace) {
				final StringWriter errors = new StringWriter();
				ex.printStackTrace(new PrintWriter(errors));
				System.out.println("Trace:");
				System.out.println(errors);
			}
			else {
				System.out.println("Use --stacktrace for stack trace");
			}
		}
	}

	private void writeVisualStatus(final SafetyResult<?, ?> status, final String filename)
			throws FileNotFoundException {
		final Graph graph = status.isSafe() ? ArgVisualizer.getDefault().visualize(status.asSafe().getArg())
				: TraceVisualizer.getDefault().visualize(status.asUnsafe().getTrace());
		GraphvizWriter.getInstance().writeFile(graph, filename);
	}

}
