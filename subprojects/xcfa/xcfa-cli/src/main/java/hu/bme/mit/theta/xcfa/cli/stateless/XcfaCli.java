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
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.NotSolvableException;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.cfa.analysis.CfaTraceConcretizer;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.cfa.cli.CfaCli;
import hu.bme.mit.theta.common.CliUtils;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.WitnessGraphvizWriter;
import hu.bme.mit.theta.common.visualization.writer.WitnessWriter;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.ComplexPortfolio;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.CpuTimeKeeper;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.ModelStatistics;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.Portfolio;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.PortfolioTimeoutException;
import hu.bme.mit.theta.xcfa.analysis.algorithmselection.SequentialPortfolio;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfig;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfigBuilder;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaTraceToWitness;
import hu.bme.mit.theta.xcfa.analysis.declarative.XcfaDeclarativeAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.XcfaDeclarativeState;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.utils.FrontendXcfaBuilder;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Path;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.time.Duration;
import java.time.LocalDateTime;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.Date;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TimeZone;
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

	File cexfile = null;
	File witnessfile = null;
	File dotwitnessfile = null;
	File highlightedxcfafile = null;
	File statisticstxtfile = null;
	File statisticscsvfile = null;
	File cfafile = null;
	File xcfafile = null;

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
//
//	@Parameter(names = "--load-store", description = "Map global memory accesses to loads and stores")
//	boolean loadStore = false;

	@Parameter(names = "--precheck", description = "Perform a pre-check when refining a multithreaded program for possibly higher efficiency", arity = 1)
	boolean preCheck = true;

	@Parameter(names = "--algorithm", description = "Algorithm to use when solving multithreaded programs")
	XcfaConfigBuilder.Algorithm algorithm = XcfaConfigBuilder.Algorithm.DECL;

	//////////// SMTLib options ////////////

	@Parameter(names = "--smt-home", description = "The path of the solver registry")
	String home = SmtLibSolverManager.HOME.toAbsolutePath().toString();

	@Parameter(names = "--abstraction-solver", description = "Sets the underlying SMT solver to use for the abstraction process. Enter in format <solver_name>:<solver_version>, see theta-smtlib-cli.jar for more details. Enter \"Z3\" to use the legacy z3 solver.")
	String abstractionSolver = "Z3";

	@Parameter(names = "--refinement-solver", description = "Sets the underlying SMT solver to use for the refinement process. Enter in format <solver_name>:<solver_version>, see theta-smtlib-cli.jar for more details. Enter \"Z3\" to use the legacy z3 solver.")
	String refinementSolver = "Z3";

	//////////// CONFIGURATION OPTIONS END ////////////

	private Logger logger;

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

		final SolverFactory abstractionSolverFactory;
		final SolverFactory refinementSolverFactory;
		try {
			// register solver managers
			SolverManager.registerSolverManager(Z3SolverManager.create());
			if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
				final var homePath = Path.of(home);
				final var smtLibSolverManager = SmtLibSolverManager.create(homePath, logger);
				SolverManager.registerSolverManager(smtLibSolverManager);
			}

			abstractionSolverFactory = SolverManager.resolveSolverFactory(abstractionSolver);
			refinementSolverFactory = SolverManager.resolveSolverFactory(refinementSolver);
		} catch (Exception e) {
			e.printStackTrace();
			return;
		}

		// portfolios and output-results uses these
		File resultsDir = new File(model + "-" + LocalDateTime.now().toString() + "-results");
		boolean bool = resultsDir.mkdir();
		if(!bool){
			throw new RuntimeException("Couldn't create results directory");
		}
		String basicFileName = resultsDir + "/" + model.getName();

		/// output results file creation
		// create filenames, if needed
		if(witnessOnly) {
			witnessfile = new File(basicFileName + ".witness.graphml");
		} else if(outputResults) {
			xcfafile = new File(basicFileName + ".xcfa");
			cfafile = new File(basicFileName + ".cfa");
			cexfile = new File(basicFileName + ".cex");
			witnessfile = new File(basicFileName + ".witness.graphml");
			dotwitnessfile = new File(basicFileName + ".witness.dot");
			highlightedxcfafile = new File(basicFileName + ".highlighted.xcfa");
			statisticstxtfile = new File(basicFileName + ".statistics.txt");
			statisticscsvfile = new File(basicFileName + ".csv");
		}

		/// set arithmetic - if it is on efficient, the parsing will change it to either integer or bitvector
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
			if(xcfafile!=null && statisticscsvfile!=null && statisticstxtfile!=null) {
				try (BufferedWriter bw = new BufferedWriter(new FileWriter(xcfafile))) {
					if(xcfa == null) xcfa = xcfaBuilder.build();
					bw.write(xcfa.toDot());
				}
				if(xcfa == null) xcfa = xcfaBuilder.build();
				ModelStatistics statistics = ModelStatistics.createXcfaStatistics(xcfa, model.getName());
				statistics.writeToCsv(statisticscsvfile);
				statistics.writeToTxt(statisticstxtfile);
			}

			if(noAnalysis) return;

			/// starting analysis
			checkState(xcfaBuilder != null, "XCFA cannot be null");
			System.err.println("Arithmetic: " + ArchitectureConfig.arithmetic);
			SafetyResult<?, ?> status = null;

			Duration initTime = Duration.of(CpuTimeKeeper.getCurrentCpuTime(), ChronoUnit.SECONDS);
			System.err.println("Time of model transformation: " + initTime.toMillis() + "ms");
			if(xcfa == null) xcfa = xcfaBuilder.build();

			switch (portfolio) {
				case NONE:
					final XcfaConfig<?, ?, ?> configuration = buildConfiguration(xcfa, abstractionSolverFactory, refinementSolverFactory);
					status = check(configuration);
					break;
				case SEQUENTIAL:
					SequentialPortfolio sequentialPortfolio = new SequentialPortfolio(logLevel, basicFileName, model.getName());
					try {
						status = sequentialPortfolio.executeAnalysis(xcfa, initTime); // check(configuration);
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
					ComplexPortfolio complexPortfolio = new ComplexPortfolio(logLevel, basicFileName, model.getName());
					try {
						status = complexPortfolio.executeAnalysis(xcfa, initTime);
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

			if (status!=null && status.isUnsafe() && witnessfile!=null) {
				writeCex(status.asUnsafe(), refinementSolverFactory);
				writeWitness(status.asUnsafe(), refinementSolverFactory);
				// writeXcfaWithCex(xcfa, status.asUnsafe());
			} else if(status!=null && status.isSafe() && witnessfile!=null) {
				writeDummyCorrectnessWitness();
			}

			long elapsed = sw.elapsed(TimeUnit.MILLISECONDS);
			sw.stop();
			System.out.println("walltime: " + elapsed + " ms");
			System.out.println("cputime: " + CpuTimeKeeper.getCurrentCpuTime() + " s");

		} catch (final Throwable ex) {
			ex.printStackTrace();
		}
	}

	private void writeDummyCorrectnessWitness() {
		String taskHash = WitnessWriter.createTaskHash(model.getAbsolutePath());
		StringBuilder dummyWitness = new StringBuilder();
		dummyWitness.append("<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">").append(System.lineSeparator()).append(
				"<key id=\"sourcecodelang\" attr.name=\"sourcecodelang\" for=\"graph\"/>").append(System.lineSeparator()).append(
				"<key id=\"witness-type\" attr.name=\"witness-type\" for=\"graph\"/>").append(System.lineSeparator()).append(
				"<key id=\"entry\" attr.name=\"entry\" for=\"node\">").append(System.lineSeparator()).append(
				"<default>false</default>").append(System.lineSeparator()).append(
				"</key>").append(System.lineSeparator()).append(
				"<key id=\"invariant\" attr.name=\"invariant\" for=\"node\">").append(System.lineSeparator()).append(
				"<default>false</default>").append(System.lineSeparator()).append(
				"</key>").append(System.lineSeparator()).append(
				"<key attr.name=\"specification\" attr.type=\"string\" for=\"graph\" id=\"specification\"/>").append(System.lineSeparator()).append(
				"<key attr.name=\"producer\" attr.type=\"string\" for=\"graph\" id=\"producer\"/>").append(System.lineSeparator()).append(
				"<key attr.name=\"programFile\" attr.type=\"string\" for=\"graph\" id=\"programfile\"/>").append(System.lineSeparator()).append(
				"<key attr.name=\"programHash\" attr.type=\"string\" for=\"graph\" id=\"programhash\"/>").append(System.lineSeparator()).append(
				"<key attr.name=\"architecture\" attr.type=\"string\" for=\"graph\" id=\"architecture\"/>").append(System.lineSeparator()).append(
				"<key attr.name=\"creationtime\" attr.type=\"string\" for=\"graph\" id=\"creationtime\"/>").append(System.lineSeparator()).append(
				"<graph edgedefault=\"directed\">").append(System.lineSeparator()).append(
				"<data key=\"witness-type\">correctness_witness</data>").append(System.lineSeparator()).append(
				"<data key=\"producer\">theta</data>").append(System.lineSeparator()).append(
				"<data key=\"specification\">CHECK( init(main()), LTL(G ! call(reach_error())) )</data>").append(System.lineSeparator()).append(
				"<data key=\"sourcecodelang\">C</data>").append(System.lineSeparator()).append(
				"<data key=\"architecture\">32bit</data>").append(System.lineSeparator()).append(
				"<data key=\"programhash\">");
				dummyWitness.append(taskHash);
				dummyWitness.append("</data>").append(System.lineSeparator()).append(
				"<data key=\"creationtime\">");

				TimeZone tz = TimeZone.getTimeZone("UTC");
				DateFormat df = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss'Z'"); // Quoted "Z" to indicate UTC, no timezone offset
				df.setTimeZone(tz);
				String ISOdate = df.format(new Date());

				dummyWitness.append(ISOdate);
				dummyWitness.append("</data>").append(System.lineSeparator()).append(
				"<data key=\"programfile\">");
				dummyWitness.append(model.getName());
				dummyWitness.append("</data>").append(System.lineSeparator()).append(
				"<node id=\"N0\">").append(System.lineSeparator()).append(
				"<data key=\"entry\">true</data>").append(System.lineSeparator()).append(
				"</node>").append(System.lineSeparator()).append(
				"</graph>").append(System.lineSeparator()).append(
				"</graphml>");

		try (BufferedWriter bw = new BufferedWriter(new FileWriter(witnessfile))) {
			bw.write(dummyWitness.toString());
		} catch (IOException ioe) {
			ioe.printStackTrace();
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
			return new XcfaConfigBuilder(domain, refinement, abstractionSolverFactory, refinementSolverFactory, algorithm)
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

	private void writeCex(final SafetyResult.Unsafe<?, ?> status, SolverFactory concretizer) throws Exception {
		@SuppressWarnings("unchecked") final Trace<XcfaDeclarativeState<?>, XcfaDeclarativeAction> trace = (Trace<XcfaDeclarativeState<?>, XcfaDeclarativeAction>) status.getTrace();
		final Trace<XcfaDeclarativeState<ExplState>, XcfaDeclarativeAction> concrTrace = XcfaTraceConcretizer.concretize(trace, concretizer);

		if(cexfile!=null) {
			final File file = cexfile;
			PrintWriter printWriter = null;
			try {
				printWriter = new PrintWriter(file);
				printWriter.write(concrTrace.toString());
			} finally {
				if (printWriter != null) {
					printWriter.close();
				}
			}
		}
	}

	private void writeWitness(final SafetyResult.Unsafe<?, ?> status, SolverFactory concretizer) throws Exception {
		@SuppressWarnings("unchecked") final Trace<XcfaDeclarativeState<?>, XcfaDeclarativeAction> trace = (Trace<XcfaDeclarativeState<?>, XcfaDeclarativeAction>) status.getTrace();
		final Trace<XcfaDeclarativeState<ExplState>, XcfaDeclarativeAction> concrTrace = XcfaTraceConcretizer.concretize(trace, concretizer);

		Graph witnessGraph = XcfaTraceToWitness.buildWitness(concrTrace);
		if(witnessfile!=null) {
			final File file = witnessfile;
			// TODO handle more input flags to get the witness' xml parameters instead of hardcoding them
			// TODO make WitnessWriter singleton
			WitnessWriter ww = WitnessWriter.createViolationWitnessWriter(model.getAbsolutePath(), "CHECK( init(main()), LTL(G ! call(reach_error())) )", false);
			try {
				ww.writeFile(witnessGraph, witnessfile.getAbsolutePath());
			} catch (FileNotFoundException e) {
				e.printStackTrace();
			}
		}
		if(dotwitnessfile!=null) {
			WitnessGraphvizWriter.getInstance().writeFile(witnessGraph, dotwitnessfile.getAbsolutePath());
		}
	}

	// TODO use XCFA instead of CFA
	private void writeXcfaWithCex(final XCFA xcfa, final SafetyResult.Unsafe<?, ?> status) throws Exception {
		@SuppressWarnings("unchecked") final Trace<CfaState<?>, CfaAction> trace = (Trace<CfaState<?>, CfaAction>) status.getTrace();
		final Trace<CfaState<ExplState>, CfaAction> concrTrace = CfaTraceConcretizer.concretize(trace, Z3SolverManager.resolveSolverFactory("Z3"));
		Set<String> cexLocations = new LinkedHashSet<>();
		Set<XcfaEdge> cexEdges = new LinkedHashSet<>();
		for (CfaState<ExplState> state : concrTrace.getStates()) {
			cexLocations.add(state.getLoc().getName());
		}
		for (CfaAction action : concrTrace.getActions()) {
			for (CFA.Edge edge : action.getEdges()) {
				Set<Object> xcfaEdges = FrontendMetadata.lookupMetadata("cfaEdge", edge);
				for (Object xcfaEdge : xcfaEdges) {
					XcfaEdge e = (XcfaEdge) xcfaEdge;
					cexEdges.add(e);
				}
			}
		}
		final File file = highlightedxcfafile;
		try (PrintWriter printWriter = new PrintWriter(file)) {
			printWriter.write(xcfa.toDot(cexLocations, cexEdges));
		}
	}
}