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
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.cfa.analysis.CfaTraceConcretizer;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfig;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.cfa.dsl.CfaWriter;
import hu.bme.mit.theta.common.CliUtils;
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
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.NotSolvableException;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;
import hu.bme.mit.theta.xcfa.algorithmselection.ComplexPortfolio;
import hu.bme.mit.theta.xcfa.algorithmselection.ModelStatistics;
import hu.bme.mit.theta.xcfa.algorithmselection.Portfolio;
import hu.bme.mit.theta.xcfa.algorithmselection.PortfolioTimeoutException;
import hu.bme.mit.theta.xcfa.algorithmselection.SequentialPortfolio;
import hu.bme.mit.theta.xcfa.algorithmselection.CpuTimeKeeper;
import hu.bme.mit.theta.xcfa.analysis.XcfaTraceToWitness;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.utils.FrontendXcfaBuilder;
import hu.bme.mit.theta.xcfa.passes.XcfaPassManager;
import hu.bme.mit.theta.xcfa.passes.procedurepass.BMC;
import hu.bme.mit.theta.xcfa.passes.procedurepass.GlobalVarsToStoreLoad;
import hu.bme.mit.theta.xcfa.passes.procedurepass.OneStmtPerEdgePass;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.time.Duration;
import java.time.LocalDateTime;
import java.time.temporal.ChronoUnit;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
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
	CfaConfigBuilder.Domain domain = CfaConfigBuilder.Domain.PRED_CART;

	@Parameter(names = "--refinement", description = "Refinement strategy")
	CfaConfigBuilder.Refinement refinement = CfaConfigBuilder.Refinement.BW_BIN_ITP;

	@Parameter(names = "--search", description = "Search strategy")
	CfaConfigBuilder.Search search = CfaConfigBuilder.Search.ERR;

	@Parameter(names = "--predsplit", description = "Predicate splitting (for predicate abstraction)")
	CfaConfigBuilder.PredSplit predSplit = CfaConfigBuilder.PredSplit.WHOLE;

	@Parameter(names = "--precgranularity", description = "Precision granularity")
	CfaConfigBuilder.PrecGranularity precGranularity = CfaConfigBuilder.PrecGranularity.LOCAL;

	@Parameter(names = "--encoding", description = "Block encoding")
	CfaConfigBuilder.Encoding encoding = CfaConfigBuilder.Encoding.LBE;

	@Parameter(names = "--maxenum", description = "Maximal number of explicitly enumerated successors (0: unlimited)")
	Integer maxEnum = 10;

	@Parameter(names = "--initprec", description = "Initial precision of abstraction")
	CfaConfigBuilder.InitPrec initPrec = CfaConfigBuilder.InitPrec.EMPTY;

	@Parameter(names = "--prunestrategy", description = "Strategy for pruning the ARG after refinement")
	PruneStrategy pruneStrategy = PruneStrategy.LAZY;

	//////////// XCFA options (experimental) ////////////

	@Parameter(names = "--gui", description = "Show GUI")
	boolean showGui = false;

	@Parameter(names = "--bmc", description = "Run BMC pre-check")
	boolean runbmc = false;

	@Parameter(names = "--load-store", description = "Map global memory accesses to loads and stores")
	boolean loadStore = false;

	@Parameter(names = "--strict-stmtlist", description = "Exactly one statement per edge")
	boolean oneStmt = false;

	//////////// CONFIGURATION OPTIONS END ////////////

	public XcfaCli(final String[] args) {
		this.args = args;
	}

	public static void main(final String[] args) {
		final XcfaCli mainApp = new XcfaCli(args);
		mainApp.run();
	}

	private void run() {
		long beginTime = System.nanoTime();
		long beginMillis = System.currentTimeMillis();
		Stopwatch timer = Stopwatch.createStarted();

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

		// portfolios and output-results uses these
		File resultsDir = new File(model + "-" + LocalDateTime.now().toString() + "-results");
		boolean bool = resultsDir.mkdir();
		if(!bool){
			throw new RuntimeException("Couldn't create results directory");
		}
		String basicFileName = resultsDir + "/" + model.getName();

		/// output results file creation
		// create filenames, if needed
		if(outputResults) {
			xcfafile = new File(basicFileName + ".xcfa");
			cfafile = new File(basicFileName + ".cfa");
			cexfile = new File(basicFileName + ".cex");
			witnessfile = new File(basicFileName + ".witness.graphml");
			dotwitnessfile = new File(basicFileName + ".witness.dot");
			highlightedxcfafile = new File(basicFileName + ".highlighted.xcfa");
			statisticstxtfile = new File(basicFileName + ".statistics.txt");
			statisticscsvfile = new File(basicFileName + ".csv");
		}

		if(loadStore) {
			XcfaPassManager.addProcedurePass(new GlobalVarsToStoreLoad());
		}
		if(oneStmt) {
			XcfaPassManager.addProcedurePass(new OneStmtPerEdgePass());
		}

		/// set arithmetic - if it is on efficient, the parsing will change it to either integer or bitvector
		ArchitectureConfig.arithmetic = arithmeticType;

		/// Starting frontend
		final Stopwatch sw = Stopwatch.createStarted();

		final CharStream input;
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

			xcfa = frontendXcfaBuilder.buildXcfa((CProgram) program);
		} catch (IOException io) {
			io.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
			System.err.println("Frontend failed!");
			System.exit(-80);
		}

		try {

			// write xcfa into file
			if(outputResults) {
				try (BufferedWriter bw = new BufferedWriter(new FileWriter(xcfafile))) {
					bw.write(xcfa.toDot());
				}
			}

			if(showGui) {
				new XcfaGui(xcfa);
				return;
			}

			if (runbmc) {
				if(xcfa.getProcesses().size() == 1) {
					checkState(xcfa.getMainProcess().getProcedures().size() == 1, "Multiple procedures are not yet supported!");
					List<XcfaEdge> cex = new BMC().getCex(xcfa.getMainProcess().getMainProcedure());
					if(cex != null) {
						System.out.println("SafetyResult Unsafe");
						return;
					}
				}

			}

			CFA cfa;
			try {
				cfa = xcfa.createCFA();
			} catch(IllegalStateException e) {
				System.out.println("XCFA not compatible with CFA, using multithreaded analyses.");
				cfa = null;
			}

			// write cfa into file and output statistics about (X)CFA and C input file
			if(outputResults && cfa!=null) {
				try (FileOutputStream filestream = new FileOutputStream(cfafile)) {
					CfaWriter.write(cfa, filestream);
				}
				ModelStatistics statistics = ModelStatistics.createCfaStatistics(cfa, model.getName());
				statistics.writeToCsv(statisticscsvfile);
				statistics.writeToTxt(statisticstxtfile);
			}

			if(noAnalysis) return;

			/// starting analysis
			if(cfa != null) {
				System.err.println("Arithmetic: " + ArchitectureConfig.arithmetic);

				SafetyResult<?, ?> status = null;

				Duration initTime = Duration.of(CpuTimeKeeper.getCurrentCpuTime(), ChronoUnit.SECONDS);
				System.err.println("Time of model transformation: " + initTime.toMillis() + "ms");

				switch (portfolio) {
					case NONE:
						final CfaConfig<?, ?, ?> configuration = buildConfiguration(cfa, cfa.getErrorLoc().get());
						status = check(configuration);
						break;
					case SEQUENTIAL:
						SequentialPortfolio sequentialPortfolio = new SequentialPortfolio(logLevel, basicFileName, model.getName());
						try {
							status = sequentialPortfolio.executeAnalysis(cfa, initTime); // check(configuration);
						} catch (PortfolioTimeoutException pte) {
							System.err.println(pte.getMessage());
							long elapsed = sw.elapsed(TimeUnit.MILLISECONDS);
							sw.stop();
							System.out.println("Millis diff: " + (System.currentTimeMillis() - beginMillis) + " ms");
							System.out.println("Nanotime diff: " + (System.nanoTime() - beginTime)/1000.0/1000.0 + " ms");
							System.out.println("walltime: " + elapsed + " ms");
							System.out.println("cputime: " + CpuTimeKeeper.getCurrentCpuTime() + " s");
							System.exit(-43); // portfolio timeout
						}
						break;
					case COMPLEX:
						ComplexPortfolio complexPortfolio = new ComplexPortfolio(logLevel, basicFileName, model.getName());
						try {
							status = complexPortfolio.executeAnalysis(cfa, initTime);
						} catch (PortfolioTimeoutException pte) {
							System.err.println(pte.getMessage());
							long elapsed = sw.elapsed(TimeUnit.MILLISECONDS);
							sw.stop();
							System.out.println("Millis diff: " + (System.currentTimeMillis() - beginMillis) + " ms");
							System.out.println("Nanotime diff: " + (System.nanoTime() - beginTime)/1000.0/1000.0 + " ms");
							System.out.println("walltime: " + elapsed + " ms");
							System.out.println("cputime: " + CpuTimeKeeper.getCurrentCpuTime() + " s");
							System.exit(-43); // portfolio timeout
						}
						break;
					default:
						throw new IllegalStateException("Unexpected value: " + portfolio);
				}

				if (status!=null && status.isUnsafe() && outputResults) {
					writeCex(status.asUnsafe());
					writeWitness(status.asUnsafe());
					writeXcfaWithCex(xcfa, status.asUnsafe());
				}
			} else {
				System.err.println("Cannot transform XCFA into CFA");
				System.exit(-50); // Cannot create CFA
				// BoundedMultithreadedAnalysis parametricAnalysis = XcfaAnalysis.createParametricAnalysis(xcfa);
			}

			long elapsed = sw.elapsed(TimeUnit.MILLISECONDS);
			sw.stop();
			System.out.println("Millis diff: " + (System.currentTimeMillis() - beginMillis) + " ms");
			System.out.println("Nanotime diff: " + (System.nanoTime() - beginTime)/1000.0/1000.0 + " ms");
			System.out.println("walltime: " + elapsed + " ms");
			System.out.println("cputime: " + CpuTimeKeeper.getCurrentCpuTime() + " s");

		} catch (final Throwable ex) {
			ex.printStackTrace();
		}
	}

	private CfaConfig<?, ?, ?> buildConfiguration(CFA cfa, CFA.Loc loc) throws Exception {
		// set up Arg-Cex check
		if(noArgCexCheck) {
			ArgCexCheckHandler.instance.setArgCexCheck(false, false);
		} else {
			if(refinement.equals(CfaConfigBuilder.Refinement.MULTI_SEQ)) {
				ArgCexCheckHandler.instance.setArgCexCheck(true, true);
			} else {
				ArgCexCheckHandler.instance.setArgCexCheck(true, false);
			}
		}

		// Build configuration
		try {
			return new CfaConfigBuilder(domain, refinement, Z3SolverFactory.getInstance())
					.precGranularity(precGranularity).search(search)
					.predSplit(predSplit).encoding(encoding).maxEnum(maxEnum).initPrec(initPrec)
					.pruneStrategy(pruneStrategy).logger(new ConsoleLogger(logLevel)).build(cfa, loc);

		} catch (final Exception ex) {
			throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
		}
	}

	private SafetyResult<?, ?> check(CfaConfig<?, ?, ?> configuration) throws Exception {
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

	private void writeCex(final SafetyResult.Unsafe<?, ?> status) throws FileNotFoundException {
		@SuppressWarnings("unchecked") final Trace<CfaState<?>, CfaAction> trace = (Trace<CfaState<?>, CfaAction>) status.getTrace();
		final Trace<CfaState<ExplState>, CfaAction> concrTrace = CfaTraceConcretizer.concretize(trace, Z3SolverFactory.getInstance());

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

	private void writeWitness(final SafetyResult.Unsafe<?, ?> status) throws FileNotFoundException {
		@SuppressWarnings("unchecked") final Trace<CfaState<?>, CfaAction> trace = (Trace<CfaState<?>, CfaAction>) status.getTrace();
		final Trace<CfaState<ExplState>, CfaAction> concrTrace = CfaTraceConcretizer.concretize(trace, Z3SolverFactory.getInstance());

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

	private void writeXcfaWithCex(final XCFA xcfa, final SafetyResult.Unsafe<?, ?> status) throws FileNotFoundException {
		@SuppressWarnings("unchecked") final Trace<CfaState<?>, CfaAction> trace = (Trace<CfaState<?>, CfaAction>) status.getTrace();
		final Trace<CfaState<ExplState>, CfaAction> concrTrace = CfaTraceConcretizer.concretize(trace, Z3SolverFactory.getInstance());
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
