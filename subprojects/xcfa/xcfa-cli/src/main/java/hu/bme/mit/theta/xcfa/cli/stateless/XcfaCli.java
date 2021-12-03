/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.cli.stateless;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.NotSolvableException;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.cfa.cli.CfaCli;
import hu.bme.mit.theta.common.CliUtils;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.validator.SolverValidatorWrapperFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.ComplexPortfolio;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.CpuTimeKeeper;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.Portfolio;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.PortfolioTimeoutException;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.SequentialPortfolio;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfig;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfigBuilder;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.utils.FrontendXcfaBuilder;
import hu.bme.mit.theta.xcfa.analysis.utils.OutputHandler;
import hu.bme.mit.theta.xcfa.analysis.utils.OutputOptions;
import hu.bme.mit.theta.xcfa.passes.procedurepass.SimpleLbePass;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.File;
import java.io.FileInputStream;
import java.nio.file.Path;
import java.time.Duration;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static com.google.common.base.Preconditions.checkState;

public class XcfaCli {
	private static final String JAR_NAME = "theta-xcfa-cli.jar";
	private final String[] args;

	//////////// CONFIGURATION OPTIONS BEGIN ////////////

	//////////// input task ////////////

	@Parameter(names = "--input", description = "Path of the input C program", required = true)
	File model;

	//////////// output data and statistics ////////////

	@Parameter(names = "--version", description = "Display version", help = true)
	boolean versionInfo = false;

	@Parameter(names = "--loglevel", description = "Detailedness of logging")
	Logger.Level logLevel = Logger.Level.MAINSTEP;

	@Parameter(names = "--output-results", description = "Beside the input file creates a directory <input>-<timestamp>-result, in which it outputs the xcfa (simple and highlighted), cex, witness (graphml and dot) and statistics (txt)", help = true)
	boolean outputResults = false;

	@Parameter(names = "--witness-only", description = "Does not output any other files, just a violation/correctness witness only")
	boolean witnessOnly = false;

	@Parameter(names = "--no-analysis", description = "Executes the model transformation to XCFA and CFA, and then exits; use with --output-results to get data about the (X)CFA")
	boolean noAnalysis = false;

	File cexfile = null; // for legacy cfa only
	File cfafile = null; // for legacy cfa only

	//////////// arithmetic types allowed ////////////

	@Parameter(names = "--arithmetic-type", description = "Arithmetic type to use when building an XCFA")
	ArchitectureConfig.ArithmeticType arithmeticType = ArchitectureConfig.ArithmeticType.efficient;

	//////////// runtime interventions ////////////

	@Parameter(names = "--portfolio", description = "Use this flag instead of the CEGAR options if you are not familiar with those; includes a 900s timeout and uses 2 threads", help = true)
	Portfolio portfolio = Portfolio.NONE;

	@Parameter(names = "--no-arg-cex-check")
	boolean noArgCexCheck = false;

	//////////// CEGAR configuration options ////////////

	@Parameter(names = "--domain", description = "Abstract domain")
	XcfaConfigBuilder.Domain domain = XcfaConfigBuilder.Domain.PRED_CART;

	@Parameter(names = "--refinement", description = "Refinement strategy")
	XcfaConfigBuilder.Refinement refinement = XcfaConfigBuilder.Refinement.BW_BIN_ITP;

	@Parameter(names = "--search", description = "Search strategy")
	XcfaConfigBuilder.Search search = XcfaConfigBuilder.Search.ERR;

	@Parameter(names = "--predsplit", description = "Predicate splitting (for predicate abstraction)")
	XcfaConfigBuilder.PredSplit predSplit = XcfaConfigBuilder.PredSplit.WHOLE;

	@Parameter(names = "--maxenum", description = "Maximal number of explicitly enumerated successors (0: unlimited)")
	Integer maxEnum = 10;

	@Parameter(names = "--initprec", description = "Initial precision of abstraction")
	XcfaConfigBuilder.InitPrec initPrec = XcfaConfigBuilder.InitPrec.EMPTY;

	@Parameter(names = "--prunestrategy", description = "Strategy for pruning the ARG after refinement")
	PruneStrategy pruneStrategy = PruneStrategy.LAZY;

	@Parameter(names = "--header", description = "Print only a header (for benchmarks) (only valid together with the -legacy switch)", help = true)
	boolean headerOnly = false;

	@Parameter(names = "--metrics", description = "Print metrics about the CFA without running the algorithm (only valid together with the -legacy switch)")
	boolean metrics = false;

	@Parameter(names = "--stacktrace", description = "Print full stack trace in case of exception (only valid together with the -legacy switch)")
	boolean stacktrace = false;

	@Parameter(names = "--autoexpl", description = "AutoExpl method to use when Product Abstraction is used")
	XcfaConfigBuilder.AutoExpl autoExpl = XcfaConfigBuilder.AutoExpl.STATIC;

	//////////// Legacy (CFA-only) options ////////////

	@Parameter(names = "--precgranularity", description = "Precision granularity (only valid together with the -legacy switch)")
	CfaConfigBuilder.PrecGranularity precGranularity = CfaConfigBuilder.PrecGranularity.LOCAL;

	@Parameter(names = "--encoding", description = "Block encoding (only valid together with the -legacy switch)")
	CfaConfigBuilder.Encoding encoding = CfaConfigBuilder.Encoding.LBE;

	@Parameter(names = "--benchmark", description = "Benchmark mode (only print metrics) (only valid together with the -legacy switch)")
	Boolean benchmarkMode = false;

	@Parameter(names = "--legacy", description = "Use legacy (cfa-cli, without portfolio) analysis when possible")
	boolean legacy = false;

	//////////// XCFA options (experimental) ////////////

//	@Parameter(names = "--load-store", description = "Map global memory accesses to loads and stores")
//	boolean loadStore = false;

	@Parameter(names = "--precheck", description = "Perform a pre-check when refining a multithreaded program for possibly higher efficiency", arity = 1)
	boolean preCheck = true;

	@Parameter(names = "--algorithm", description = "Algorithm to use when solving multithreaded programs")
	XcfaConfigBuilder.Algorithm algorithm = XcfaConfigBuilder.Algorithm.SINGLETHREAD;

	//////////// SMTLib options ////////////

	@Parameter(names = "--smt-home", description = "The path of the solver registry")
	String home = SmtLibSolverManager.HOME.toAbsolutePath().toString();

	@Parameter(names = "--abstraction-solver", description = "Sets the underlying SMT solver to use for the abstraction process. Enter in format <solver_name>:<solver_version>, see theta-smtlib-cli.jar for more details. Enter \"Z3\" to use the legacy z3 solver.")
	String abstractionSolver = "Z3";

	@Parameter(names = "--refinement-solver", description = "Sets the underlying SMT solver to use for the refinement process. Enter in format <solver_name>:<solver_version>, see theta-smtlib-cli.jar for more details. Enter \"Z3\" to use the legacy z3 solver.")
	String refinementSolver = "Z3";

	@Parameter(names = "--validate-refinement-solver", description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
	boolean validateRefinementSolver = false;

	@Parameter(names = "--validate-abstraction-solver", description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
	boolean validateAbstractionSolver = false;

	@Parameter(names = "--lbe", description = "Large-block encoding level")
	SimpleLbePass.LBELevel lbeLevel = SimpleLbePass.LBELevel.NO_LBE;

	//////////// CONFIGURATION OPTIONS END ////////////

	private Logger logger = new ConsoleLogger(logLevel);;

	public XcfaCli(final String[] args) {
		this.args = args;
	}

	public static void main(final String[] args) {
		final XcfaCli mainApp = new XcfaCli(args);
		mainApp.run();
	}

	private void run() {
		/// Checking flags
		try {
			JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(args);
		} catch (final ParameterException ex) {
			System.out.println("Invalid parameters, details:");
			System.out.println(ex.getMessage());
			ex.usage();
			return;
		}

		/// version
		if (versionInfo) {
			CliUtils.printVersion(System.out);
			return;
		}

		SimpleLbePass.level = lbeLevel;

		// TODO later we might want to merge these two flags
		if(witnessOnly) {
			OutputHandler.create(OutputOptions.WITNESS_ONLY, model);
		} else if(outputResults) {
			OutputHandler.create(OutputOptions.OUTPUT_RESULTS, model);
		} else {
			OutputHandler.create(OutputOptions.NONE, model);
		}
		OutputHandler.getInstance().createResultsDirectory();

		// set arithmetic - if it is on efficient, the parsing will change it to either integer or bitvector
		ArchitectureConfig.arithmetic = arithmeticType;

		/// Starting frontend
		final Stopwatch sw = Stopwatch.createStarted();

		final CharStream input;
		XCFA.Builder xcfaBuilder = null;
		XCFA xcfa = null;
		try {
			input = CharStreams.fromStream(new FileInputStream(model));
			final CLexer lexer = new CLexer(input);
			final CommonTokenStream tokens = new CommonTokenStream(lexer);
			final CParser parser = new CParser(tokens);
			final CParser.CompilationUnitContext context = parser.compilationUnit();

			CStatement program = context.accept(FunctionVisitor.instance);
			checkState(program instanceof CProgram, "Parsing did not return a program!");

			FrontendXcfaBuilder frontendXcfaBuilder = new FrontendXcfaBuilder();

			xcfaBuilder = frontendXcfaBuilder.buildXcfa((CProgram) program);
		} catch (Exception e) {
			e.printStackTrace();
			System.err.println("Frontend failed!");
			System.exit(-80);
		}

		try {
			if(legacy) {
				CFA cfa;
				try {
					if(xcfa == null) xcfa = xcfaBuilder.build();
					cfa = xcfa.createCFA();
				} catch(IllegalStateException e) {
					System.out.println("XCFA not compatible with CFA, using multithreaded analyses.");
					cfa = null;
				}
				if(cfa != null) {
					List<String> args = new ArrayList<>();
					args.add("--domain"); args.add(domain.name());
					args.add("--refinement"); args.add(refinement.name());
					args.add("--search"); args.add(search.name());
					args.add("--predsplit"); args.add(predSplit.name());
					args.add("--model"); args.add(model.getAbsolutePath());
					// args.add("--errorloc"); args.add(cfa.getErrorLoc().get().getName());
					args.add("--precgranularity"); args.add(precGranularity.name());
					args.add("--encoding"); args.add(encoding.name());
					args.add("--maxenum"); args.add(maxEnum.toString());
					args.add("--initprec"); args.add(initPrec.name());
					args.add("--prunestrategy"); args.add(pruneStrategy.name());
					args.add("--loglevel"); args.add(logLevel.name());
					if(benchmarkMode) args.add("--benchmark");
					if(cexfile!=null && cfafile!=null) {
						args.add("--cex"); args.add(cexfile.getAbsolutePath());
						args.add("--visualize"); args.add(cfafile.getAbsolutePath());
					}
					if(headerOnly) args.add("--header");
					if(metrics) args.add("--metrics");
					if(stacktrace) args.add("--stacktrace");

					CfaCli.main((String[]) args.toArray());
					return;
				}
			}

			// write cfa into file and output statistics about (X)CFA and C input file
			if(xcfa == null) xcfa = xcfaBuilder.build();
			OutputHandler.getInstance().writeXcfa(xcfa);
			OutputHandler.getInstance().writeInputStatistics(xcfa);

			if(noAnalysis) return;

			/// Checks, preparation and info output before analysis
			checkState(xcfaBuilder != null, "XCFA cannot be null");
			SafetyResult<?, ?> status = null;

			Duration initTime = Duration.of(CpuTimeKeeper.getCurrentCpuTime(), ChronoUnit.SECONDS);
			logger.write(Logger.Level.RESULT, "Time of model transformation: " + initTime.toMillis() + "ms" + System.lineSeparator());

			try {
				registerAllSolverManagers(home, logger);
			} catch (Exception e) {
				e.printStackTrace();
				return;
			}

			/// starting analysis
			switch (portfolio) {
				case NONE:
					try {
						executeSingleConfiguration(xcfa);
					} catch (Exception e) {
						e.printStackTrace();
						return;
					}
					break;
				case SEQUENTIAL:
					SequentialPortfolio sequentialPortfolio = new SequentialPortfolio(logLevel, model.getName(), home);
					try {
						sequentialPortfolio.executeAnalysis(xcfa, initTime); // check(configuration);
					} catch (PortfolioTimeoutException pte) {
						System.err.println(pte.getMessage());
						long elapsed = sw.elapsed(TimeUnit.MILLISECONDS);
						sw.stop();
						System.out.println("walltime: " + elapsed + " ms");
						System.out.println("cputime: " + CpuTimeKeeper.getCurrentCpuTime() + " s");
						System.exit(-43); // portfolio timeout
					}
					break;
				case COMPLEX:
					ComplexPortfolio complexPortfolio = new ComplexPortfolio(logLevel, model.getName(), home);
					try {
						complexPortfolio.executeAnalysis(xcfa, initTime);
					} catch (PortfolioTimeoutException pte) {
						System.err.println(pte.getMessage());
						long elapsed = sw.elapsed(TimeUnit.MILLISECONDS);
						sw.stop();
						System.out.println("walltime: " + elapsed + " ms");
						System.out.println("cputime: " + CpuTimeKeeper.getCurrentCpuTime() + " s");
						System.exit(-43); // portfolio timeout
					}
					break;
				default:
					throw new IllegalStateException("Unexpected value: " + portfolio);
			}

			long elapsed = sw.elapsed(TimeUnit.MILLISECONDS);
			sw.stop();
			System.out.println("walltime: " + elapsed + " ms");
			System.out.println("cputime: " + CpuTimeKeeper.getCurrentCpuTime() + " s");

		} catch (final Throwable ex) {
			ex.printStackTrace();
		}
	}

	public static void registerAllSolverManagers(String home, Logger logger) throws Exception {
		CpuTimeKeeper.saveSolverTimes();
		SolverManager.closeAll();
		// register solver managers
		SolverManager.registerSolverManager(Z3SolverManager.create());
		if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
			final var homePath = Path.of(home);
			final var smtLibSolverManager = SmtLibSolverManager.create(homePath, logger);
			SolverManager.registerSolverManager(smtLibSolverManager);
		}
	}

	private void executeSingleConfiguration(XCFA xcfa) throws Exception {
		final SolverFactory abstractionSolverFactory;
		final SolverFactory refinementSolverFactory;
		if(validateRefinementSolver) {
			refinementSolverFactory = SolverValidatorWrapperFactory.create(refinementSolver);
		} else {
			refinementSolverFactory = SolverManager.resolveSolverFactory(refinementSolver);
		}
		if(validateAbstractionSolver) {
			abstractionSolverFactory = SolverValidatorWrapperFactory.create(abstractionSolver);
		} else {
			abstractionSolverFactory = SolverManager.resolveSolverFactory(abstractionSolver);
		}

		final XcfaConfig<?, ?, ?> configuration = buildConfiguration(xcfa, abstractionSolverFactory, refinementSolverFactory);
		SafetyResult<?, ?> status = check(configuration);
		if (status!=null && status.isUnsafe()) {
			OutputHandler.getInstance().writeCounterexamples(status, refinementSolver);
		} else if(status!=null && status.isSafe()) {
			OutputHandler.getInstance().writeDummyCorrectnessWitness();
		}
	}

	private XcfaConfig<?, ?, ?> buildConfiguration(XCFA xcfa, SolverFactory abstractionSolverFactory, SolverFactory refinementSolverFactory) throws Exception {
		// set up Arg-Cex check
		if(noArgCexCheck) {
			ArgCexCheckHandler.instance.setArgCexCheck(false, false);
		} else {
			if(refinement.equals(XcfaConfigBuilder.Refinement.MULTI_SEQ)) {
				ArgCexCheckHandler.instance.setArgCexCheck(true, true);
			} else {
				ArgCexCheckHandler.instance.setArgCexCheck(true, false);
			}
		}

		// Build configuration
		try {
			return new XcfaConfigBuilder(domain, refinement, refinementSolverFactory, abstractionSolverFactory, algorithm)
					.search(search).predSplit(predSplit).maxEnum(maxEnum).initPrec(initPrec).preCheck(preCheck)
					.pruneStrategy(pruneStrategy).logger(new ConsoleLogger(logLevel)).autoExpl(autoExpl).build(xcfa);

		} catch (final Exception ex) {
			throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
		}
	}

	private SafetyResult<?, ?> check(XcfaConfig<?, ?, ?> configuration) throws Exception {
		try {
			return configuration.check();
		} catch (final NotSolvableException exception) {
			System.err.println("Configuration failed (stuck)");
			System.exit(-30);
			throw exception;
		} catch (final Exception ex) {
			String message = ex.getMessage() == null ? "(no message)" : ex.getMessage();
			throw new Exception("Error while running algorithm: " + ex.getClass().getSimpleName() + " " + message, ex);
		}
	}


}