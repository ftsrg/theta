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
import java.nio.file.Path;
import java.util.concurrent.TimeUnit;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;

import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.utils.TraceVisualizer;
import hu.bme.mit.theta.common.CliUtils;
import hu.bme.mit.theta.common.OsHelper;
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
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.XtaVisualizer;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.xta.analysis.config.XtaConfig;
import hu.bme.mit.theta.xta.analysis.config.XtaConfigBuilder;
import hu.bme.mit.theta.xta.analysis.lazy.ClockStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.DataStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaCheckerFactory;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;

import javax.sound.sampled.AudioFormat;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.xta.analysis.config.XtaConfigBuilder.*;

public final class XtaCli {
	private static final String JAR_NAME = "theta-xta.jar";
	private final String[] args;
	private final TableWriter writer;

	@Parameter(names = {"--model", "-m"}, description = "Path of the input model", required = true)
	String model;

	@Parameter(names = {"--discrete", "-d"}, description = "Refinement strategy for discrete variables", required = false)
	DataStrategy dataStrategy = DataStrategy.NONE;

	@Parameter(names = {"--clock", "-c"}, description = "Refinement strategy for clock variables", required = true)
	ClockStrategy clockStrategy;

	@Parameter(names = {"--search", "-s"}, description = "Search strategy", required = true)
	SearchStrategy searchStrategy;

	@Parameter(names = {"--benchmark", "-b"}, description = "Benchmark mode (only print metrics)")
	Boolean benchmarkMode = false;

	@Parameter(names = {"--visualize", "-v"}, description = "Write proof or counterexample to file in dot format")
	String dotfile = null;

	@Parameter(names = {"--header", "-h"}, description = "Print only a header (for benchmarks)", help = true)
	boolean headerOnly = false;

	@Parameter(names = "--stacktrace", description = "Print full stack trace in case of exception")
	boolean stacktrace = false;

	@Parameter(names = "--version", description = "Display version", help = true)
	boolean versionInfo = false;

	//Eager CEGAR
	@Parameter(names = {"--checkmethod", "-cm"}, description = "Check the model with Eager-CEGAR, or Lazy-Abstraction", required = true)
	String method;
	@Parameter(names = "--domain", description = "Abstract domain")
	Domain domain = Domain.PRED_CART;

	@Parameter(names = "--refinement", description = "Refinement strategy")
	Refinement refinement = Refinement.SEQ_ITP;

	@Parameter(names = "--search", description = "Search strategy")
	Search search = Search.BFS;

	@Parameter(names = "--predsplit", description = "Predicate splitting (for predicate abstraction)")
	PredSplit predSplit = PredSplit.WHOLE;

	@Parameter(names = "--solver", description = "Sets the underlying SMT solver to use for both the abstraction and the refinement process. Enter in format <solver_name>:<solver_version>, see theta-smtlib-cli.jar for more details. Enter \"Z3\" to use the legacy z3 solver.")
	String solver = "Z3";

	@Parameter(names = "--abstraction-solver", description = "Sets the underlying SMT solver to use for the abstraction process. Enter in format <solver_name>:<solver_version>, see theta-smtlib-cli.jar for more details. Enter \"Z3\" to use the legacy z3 solver.")
	String abstractionSolver;

	@Parameter(names = "--refinement-solver", description = "Sets the underlying SMT solver to use for the refinement process. Enter in format <solver_name>:<solver_version>, see theta-smtlib-cli.jar for more details. Enter \"Z3\" to use the legacy z3 solver.")
	String refinementSolver;


	@Parameter(names = "--precgranularity", description = "Precision granularity")
	PrecGranularity precGranularity = PrecGranularity.GLOBAL;

	@Parameter(names = "--maxenum", description = "Maximal number of explicitly enumerated successors (0: unlimited)")
	Integer maxEnum = 10;

	@Parameter(names = "--initprec", description = "Initial precision of abstraction")
	InitPrec initPrec = InitPrec.EMPTY;

	@Parameter(names = "--prunestrategy", description = "Strategy for pruning the ARG after refinement")
	PruneStrategy pruneStrategy = PruneStrategy.LAZY;

	@Parameter(names = "--loglevel", description = "Detailedness of logging")
	Logger.Level logLevel = Logger.Level.SUBSTEP;


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
			if(method.equals("eager")){
				Eager_Cegar_check();
				return;
			}
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
			final SafetyChecker<?, ?, UnitPrec> checker = LazyXtaCheckerFactory.create(system, dataStrategy,
					clockStrategy, searchStrategy);
			final SafetyResult<?, ?> result = check(checker);
			printResult(result);
			if (dotfile != null) {
				writeVisualStatus(result, dotfile);
			}
		} catch (final Throwable ex) {
			printError(ex);
			System.exit(1);
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
		} catch (Exception ex) {
			throw new Exception("Could not parse XTA: " + ex.getMessage(), ex);
		}
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

	private void Eager_Cegar_check(){
		final SolverFactory abstractionSolverFactory;
		try {
			SolverManager.registerSolverManager(Z3SolverManager.create());
			if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
				final var homePath = Path.of(home);
				final var smtLibSolverManager = SmtLibSolverManager.create(homePath, logger);
				SolverManager.registerSolverManager(smtLibSolverManager);
			}

			final Stopwatch sw = Stopwatch.createStarted();
			final XtaSystem xta = loadModel();

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
			printResult(status);
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
			return new XtaConfigBuilder(domain, refinement, abstractionSolverFactory, refinementSolverFactory)
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


