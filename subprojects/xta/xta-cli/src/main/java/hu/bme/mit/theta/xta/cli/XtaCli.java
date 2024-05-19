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

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.utils.TraceVisualizer;
import hu.bme.mit.theta.common.CliUtils;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.common.table.BasicTableWriter;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.XtaVisualizer;
import hu.bme.mit.theta.xta.analysis.config.XtaConfig;
import hu.bme.mit.theta.xta.analysis.config.XtaConfigBuilder_ClockPred;
import hu.bme.mit.theta.xta.analysis.config.XtaConfigBuilder_Zone;
import hu.bme.mit.theta.xta.analysis.lazy.ClockStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import hu.bme.mit.theta.xta.utils.CTLOperatorNotSupportedException;
import hu.bme.mit.theta.xta.utils.MixedDataTimeNotSupportedException;

import java.io.*;
import java.nio.file.Path;

import static hu.bme.mit.theta.xta.analysis.config.XtaConfigBuilder_Zone.*;

public final class XtaCli {

	public enum Algorithm {
		EAGER
	}

	private static final String JAR_NAME = "theta-xta.jar";
	private final String[] args;
	private final TableWriter writer;

	@Parameter(names = {"--model", "-m"}, description = "Path of the input model", required = true)
	String model;

	@Parameter (names = {"--clockpred"}, description = "Use clock predicate domain")
	boolean clockpred = false;
	/*@Parameter(names = {"--discreteconcr", "-dc"}, description = "Concrete domain for discrete variables", required = false)
	DataStrategy2.ConcrDom concrDataDom = DataStrategy2.ConcrDom.EXPL;

	@Parameter(names = {"--discreteabstr", "-da"}, description = "Abstract domain for discrete variables", required = false)
	DataStrategy2.AbstrDom abstrDataDom = DataStrategy2.AbstrDom.EXPL;

	@Parameter(names = {"--discreteitp", "-di"}, description = "Interpolation strategy for discrete variables", required = false)
	DataStrategy2.ItpStrategy dataItpStrategy = DataStrategy2.ItpStrategy.BIN_BW;

	@Parameter(names = {"--meet", "-me"}, description = "Meet strategy for expressions", required = false)
	ExprMeetStrategy exprMeetStrategy = ExprMeetStrategy.BASIC;*/

	@Parameter(names = {"--clock", "-c"}, description = "Refinement strategy for clock variables", required = false)
	ClockStrategy clockStrategy = ClockStrategy.BWITP;

	@Parameter(names = {"--algorithm"}, description = "")
	Algorithm algorithm = Algorithm.EAGER;

	@Parameter(names = {"--benchmark", "-b"}, description = "Benchmark mode (only print metrics)")
	Boolean benchmarkMode = false;

	@Parameter(names = {"--header", "-h"}, description = "Print only a header (for benchmarks)", help = true)
	boolean headerOnly = false;

	@Parameter(names = "--stacktrace", description = "Print full stack trace in case of exception")
	boolean stacktrace = false;

	@Parameter(names = "--loglevel", description = "Detailedness of logging")
	Logger.Level logLevel = Logger.Level.MAINSTEP;

	@Parameter(names = "--version", description = "Display version", help = true)
	boolean versionInfo = false;

	//Eager CEGAR
	@Parameter(names = "--domain", description = "Abstract domain")
	String domain = "PRED_CART";

	@Parameter(names = "--refinement", description = "Refinement strategy")
	String refinement = "SEQ_ITP";

	@Parameter(names = "--search", description = "Search strategy")
	String search = "BFS";

	@Parameter(names = "--predsplit", description = "Predicate splitting (for predicate abstraction)")
	String predSplit = "WHOLE";

	@Parameter(names = "--solver", description = "Sets the underlying SMT solver to use for both the abstraction and the refinement process. Enter in format <solver_name>:<solver_version>, see theta-smtlib-cli.jar for more details. Enter \"Z3\" to use the legacy z3 solver.")
	String solver = "Z3";

	@Parameter(names = "--abstraction-solver", description = "Sets the underlying SMT solver to use for the abstraction process. Enter in format <solver_name>:<solver_version>, see theta-smtlib-cli.jar for more details. Enter \"Z3\" to use the legacy z3 solver.")
	String abstractionSolver;

	@Parameter(names = "--refinement-solver", description = "Sets the underlying SMT solver to use for the refinement process. Enter in format <solver_name>:<solver_version>, see theta-smtlib-cli.jar for more details. Enter \"Z3\" to use the legacy z3 solver.")
	String refinementSolver;


	@Parameter(names = "--precgranularity", description = "Precision granularity")
	String precGranularity = "GLOBAL";

	@Parameter(names = "--maxenum", description = "Maximal number of explicitly enumerated successors (0: unlimited)")
	Integer maxEnum = 0;

	@Parameter(names = "--initprec", description = "Initial precision of abstraction")
	String initPrec = "EMPTY";

	@Parameter(names = "--prunestrategy", description = "Strategy for pruning the ARG after refinement")
	PruneStrategy pruneStrategy = PruneStrategy.LAZY;

	@Parameter(names = "--cex", description = "Write concrete counterexample to a file")
	String cexfile = null;


	@Parameter(names = "--visualize", description = "Visualize CFA to this file without running the algorithm")
	String visualize = null;

	@Parameter(names = "--metrics", description = "Print metrics about the CFA without running the algorithm")
	boolean metrics = false;
	@Parameter(names = "--home", description = "The path of the solver registry")
	String home = SmtLibSolverManager.HOME.toAbsolutePath().toString();


	private Logger logger;
	//eager params end

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
			logger = benchmarkMode ? NullLogger.getInstance() : new ConsoleLogger(logLevel);
		} catch (final ParameterException ex) {
			System.out.println("Invalid parameters, details:");
			System.out.println(ex.getMessage());
			ex.usage();
			return;
		}
		try {
		} catch (Throwable ex) {
			printError(ex);
			System.exit(1);
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
				//case LAZY -> runLazy(system);
				//case EXPERIMENTAL_EAGERLAZY -> runCombined(system);
				case EAGER -> runEager(system);
			}
		} catch (final Throwable ex) {
			printError(ex);
			System.exit(1);
		}
	}

	/*private void runLazy(final XtaSystem system) {
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
	}*/

	private void runEager(XtaSystem system){
		Eager_Cegar_check(system);
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

	private void Eager_Cegar_check(XtaSystem xta){
		final SolverFactory abstractionSolverFactory;
		try {
			SolverManager.registerSolverManager(Z3SolverManager.create());
			if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
				final var homePath = Path.of(home);
				final var smtLibSolverManager = SmtLibSolverManager.create(homePath, logger);
				SolverManager.registerSolverManager(smtLibSolverManager);
			}

			final Stopwatch sw = Stopwatch.createStarted();

			if (visualize != null) {
				final Graph graph = XtaVisualizer.visualize(xta);
				GraphvizWriter.getInstance().writeFileAutoConvert(graph, visualize);
				return;
			}

			if(abstractionSolver != null) {
				abstractionSolverFactory = SolverManager.resolveSolverFactory(abstractionSolver);
			}
			else {
				abstractionSolverFactory = SolverManager.resolveSolverFactory(solver);
			}


			final SolverFactory refinementSolverFactory;
			if(refinementSolver != null) {
				refinementSolverFactory = SolverManager.resolveSolverFactory(refinementSolver);
			}
			else {
				refinementSolverFactory = SolverManager.resolveSolverFactory(solver);
			}

			final XtaConfig<?, ?, ?> configuration = buildConfiguration(xta, abstractionSolverFactory, refinementSolverFactory);
			final SafetyResult<?, ?> status = check(configuration);
			sw.stop();
			System.out.println(status.isSafe());
			resultPrinter(status.isSafe(), status.isUnsafe(), xta);
			if (status.isUnsafe() && cexfile != null) {
				writeCex(status.asUnsafe());
			}
		} catch (final Throwable ex) {
			printError(ex);
			System.exit(1);
		}

	}
	private XtaConfig<?, ?, ?> buildConfiguration(final XtaSystem xta, final SolverFactory abstractionSolverFactory, final SolverFactory refinementSolverFactory) throws Exception {
		try {
			if (clockpred) {
				XtaConfigBuilder_ClockPred.Domain domainEnum = XtaConfigBuilder_ClockPred.Domain.valueOf(domain);
				XtaConfigBuilder_ClockPred.Refinement refinementEnum = XtaConfigBuilder_ClockPred.Refinement.valueOf(refinement);
				return new XtaConfigBuilder_ClockPred(domainEnum, refinementEnum, abstractionSolverFactory, refinementSolverFactory)
						.precGranularity(precGranularity).search(search)
						.predSplit(predSplit).maxEnum(maxEnum).initPrec(initPrec)
						.pruneStrategy(pruneStrategy).logger(logger).build(xta);
			}
			XtaConfigBuilder_Zone.Domain domainEnum = XtaConfigBuilder_Zone.Domain.valueOf(domain);
			XtaConfigBuilder_Zone.Refinement refinementEnum = XtaConfigBuilder_Zone.Refinement.valueOf(refinement);
			return new XtaConfigBuilder_Zone(domainEnum, refinementEnum, abstractionSolverFactory, refinementSolverFactory)
					.precGranularity(precGranularity).search(search)
					.predSplit(predSplit).maxEnum(maxEnum).initPrec(initPrec)
					.pruneStrategy(pruneStrategy).logger(logger).build(xta);
		} catch (final Exception ex) {
			throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
		}
	}

	private SafetyResult<?, ?> check(XtaConfig<?, ?, ?> configuration) throws Exception {
		try {
			return configuration.check();
		} catch (final Exception ex) {
			String message = ex.getMessage() == null ? "(no message)" : ex.getMessage();
			throw new Exception("Error while running algorithm: " + ex.getClass().getSimpleName() + " " + message, ex);
		}
	}

	private void writeCex(final SafetyResult.Unsafe<?, ?> status) throws FileNotFoundException {
		/*@SuppressWarnings("unchecked") final Trace<XtaState<?>, XtaAction> trace;
		trace = (Trace<XtaState<?>, XtaAction>) status.getTrace();
		final Trace<XtaState<ExplState>, XtaAction> concrTrace = XtaTraceConcretizer.concretize(trace, Z3SolverFactory.getInstance());
		final File file = new File(cexfile);
		PrintWriter printWriter = null;
		try {
			printWriter = new PrintWriter(file);
			printWriter.write(concrTrace.toString());
		} finally {
			if (printWriter != null) {
				printWriter.close();
			}
		}*/
	}

}


