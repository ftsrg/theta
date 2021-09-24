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
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.cfa.analysis.CfaTraceConcretizer;
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
import hu.bme.mit.theta.xcfa.algorithmselection.MaxEnumAnalyzer;
import hu.bme.mit.theta.xcfa.algorithmselection.NotSolvableException;
import hu.bme.mit.theta.xcfa.algorithmselection.PortfolioNotSolvableThrower;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfig;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfigBuilder;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaTraceToWitness;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.utils.FrontendXcfaBuilder;
import hu.bme.mit.theta.xcfa.passes.XcfaPassManager;
import hu.bme.mit.theta.xcfa.passes.procedurepass.GlobalVarsToStoreLoad;
import hu.bme.mit.theta.xcfa.passes.procedurepass.OneStmtPerEdgePass;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.time.LocalDateTime;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import static com.google.common.base.Preconditions.checkState;

public class XcfaCli {
	private static final String JAR_NAME = "theta-xcfa-cli.jar";
	private final String[] args;

	@Parameter(names = "--input", description = "Path of the input C program", required = true)
	File model;

	@Parameter(names = "--output-results", description = "Beside the input file creates a directory <input>-<timestamp>-result, in which it outputs the xcfa (simple and highlighted), cex, witness (graphml and dot) and statistics (txt)", required = false)
	boolean outputResults = false;

	// @Parameter(names = "--cex", description = "Write concrete counterexample to a file")
	String cexfile = null;

	//@Parameter(names = "--witness", description = "Write witness to a file")
	String witnessfile = null;

	//@Parameter(names = "--dot-witness", description = "Write witness to a file, but in the dot format")
	String dotwitnessfile = null;

	//@Parameter(names = "--cex-highlighted", description = "Write the XCFA with a concrete counterexample to a file")
	String highlighted = null;

	//@Parameter(names = "--statistics", description = "Write CFA statistics to a file (in a simple textual format)")
	String statisticsfile = null;

	// @Parameter(names = "--print-xcfa", description = "Print XCFA (as a dotfile) and exit.")
	String printxcfa = null;

	@Parameter(names = "--portfolio", description = "Use the built-in portfolio configurations")
	boolean portfolio;

	@Parameter(names = "--arithmetic-type", description = "Arithmetic type to use when building an XCFA")
	ArchitectureConfig.ArithmeticType arithmeticType = ArchitectureConfig.ArithmeticType.efficient;

	@Parameter(names = "--print-cfa", description = "Print CFA and exit.")
	boolean printcfa;

	@Parameter(names = "--estimateMaxEnum", description = "Estimate maxenum automatically; overwrites the value of the --maxenum flag.")
	boolean estimateMaxEnum;

	@Parameter(names = "--timeout", description = "Seconds until timeout (not precise)")
	Long timeS = Long.MAX_VALUE;

	@Parameter(names = "--version", description = "Display version", help = true)
	boolean versionInfo = false;

	@Parameter(names = "--benchmark-parsing", description = "Run parsing tasks only")
	boolean parsing = false;

	@Parameter(names = "--load-store", description = "Map global memory accesses to loads and stores")
	boolean loadStore = false;

	@Parameter(names = "--strict-stmtlist", description = "Exactly one statement per edge")
	boolean oneStmt = false;

	@Parameter(names = "--loglevel", description = "Detailedness of logging")
	Logger.Level logLevel = Logger.Level.MAINSTEP;

	@Parameter(names = "--domain", description = "Abstract domain")
	XcfaConfigBuilder.Domain domain = XcfaConfigBuilder.Domain.PRED_CART;

	@Parameter(names = "--refinement", description = "Refinement strategy")
	XcfaConfigBuilder.Refinement refinement = XcfaConfigBuilder.Refinement.BW_BIN_ITP;

	@Parameter(names = "--search", description = "Search strategy")
	XcfaConfigBuilder.Search search = XcfaConfigBuilder.Search.BFS;

	@Parameter(names = "--predsplit", description = "Predicate splitting (for predicate abstraction)")
	XcfaConfigBuilder.PredSplit predSplit = XcfaConfigBuilder.PredSplit.WHOLE;

	@Parameter(names = "--maxenum", description = "Maximal number of explicitly enumerated successors (0: unlimited)")
	Integer maxEnum = 40;

	@Parameter(names = "--algorithm", description = "Solver to use (INT_DPOR for DPOR, INT_ALL for all interleavings)")
	XcfaConfigBuilder.Algoritm algorithm = XcfaConfigBuilder.Algoritm.INT_DPOR;

	@Parameter(names = "--initprec", description = "Initial precision of abstraction")
	XcfaConfigBuilder.InitPrec initPrec = XcfaConfigBuilder.InitPrec.EMPTY;

	@Parameter(names = "--prunestrategy", description = "Strategy for pruning the ARG after refinement")
	PruneStrategy pruneStrategy = PruneStrategy.LAZY;

	public XcfaCli(final String[] args) {
		this.args = args;
	}

	public static void main(final String[] args) {
		final XcfaCli mainApp = new XcfaCli(args);
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

		if (versionInfo) {
			CliUtils.printVersion(System.out);
			return;
		}

		ArchitectureConfig.arithmetic = arithmeticType;
		if(estimateMaxEnum) {
			MaxEnumAnalyzer.enabled = true;
		} else {
			MaxEnumAnalyzer.enabled = false;
		}

		try {
			if(outputResults) {
				File resultsDir = new File(model + "-" + LocalDateTime.now().toString() + "-results");
				boolean bool = resultsDir.mkdir();
				if(!bool){
					throw new RuntimeException("Couldn't create results directory");
				}

				String basicFileName = resultsDir + "/" + model.getName();
				printxcfa = basicFileName + ".xcfa";
				printcfa = true;
//				cexfile = basicFileName + ".cex";
				witnessfile = basicFileName + ".witness.graphml";
				dotwitnessfile = basicFileName + ".witness.dot";
//				highlighted = basicFileName + ".highlighted.xcfa";
				statisticsfile = basicFileName + ".statistics.txt";
			}


			if(loadStore) {
				XcfaPassManager.addProcedurePass(new GlobalVarsToStoreLoad());
			}
			if(oneStmt) {
				XcfaPassManager.addProcedurePass(new OneStmtPerEdgePass());
			}

			final Stopwatch sw = Stopwatch.createStarted();

			final CharStream input = CharStreams.fromStream(new FileInputStream(model));

			final CLexer lexer = new CLexer(input);
			final CommonTokenStream tokens = new CommonTokenStream(lexer);
			final CParser parser = new CParser(tokens);

			final CParser.CompilationUnitContext context = parser.compilationUnit();

			CStatement program = context.accept(FunctionVisitor.instance);
			checkState(program instanceof CProgram, "Parsing did not return a program!");
			FrontendXcfaBuilder frontendXcfaBuilder = new FrontendXcfaBuilder();
			XCFA xcfa = frontendXcfaBuilder.buildXcfa((CProgram) program);

			if(parsing) {
				System.out.println("XCFA creation successful");
				try{
					CFA cfa = xcfa.createCFA();
					System.out.println("CFA creation successful");
				} catch(IllegalStateException ex) {
					System.out.println("CFA creation unsuccessful. Reason: " + ex.getMessage());
				}
				return;
			}

			if(estimateMaxEnum) {
				System.out.println("Estimated maxEnum: " + MaxEnumAnalyzer.instance.estimateMaxEnum().intValue());
//				maxEnum = MaxEnumAnalyzer.instance.estimateMaxEnum().intValue();
			}

			if (printxcfa!=null) {
				File xcfafile = new File(printxcfa);
				try (BufferedWriter bw = new BufferedWriter(new FileWriter(xcfafile))) {
					bw.write(xcfa.toDot());
				}
			}
//			if (printcfa) {
//				CFA cfa = xcfa.createCFA();
//				File cfafile = new File(model.getAbsolutePath() + ".cfa");
//				try (BufferedWriter bw = new BufferedWriter(new FileWriter(cfafile))) {
//					bw.write(cfa.toString());
//				}
//			}




//			final XcfaConfig<?, ?, ?> config = new XcfaConfigBuilder(domain, refinement, Z3SolverFactory.getInstance())
//					.precGranularity(precGranularity).search(search)
//					.predSplit(predSplit).encoding(encoding).maxEnum(maxEnum).initPrec(initPrec)
//					.pruneStrategy(pruneStrategy).logger(new ConsoleLogger(logLevel)).build(xcfa, err);
//			final SafetyResult<?, ?> status = check(config);

//			if(status.isUnsafe()) {
//				System.err.println("Unsafe");
//			}
//			else {
//				System.err.println("Safe");
//			}

//			CFA cfa;
//			try {
//				cfa = xcfa.createCFA();
//			} catch(IllegalStateException e) {
//				System.out.println("XCFA not compatible with CFA, using multithreaded analyses.");
//				cfa = null;
//			}
			if(xcfa != null) {
				final SafetyResult<?, ?> status;
				final XcfaConfig<?, ?, ?> configuration = buildConfiguration(xcfa);
				CegarChecker.setNotSolvableThrower(new PortfolioNotSolvableThrower(true));
				status = check(configuration);

				if (status.isUnsafe() && cexfile != null) {
					writeCex(status.asUnsafe());
				}
				if (status.isUnsafe() && highlighted != null) {
					writeXcfaWithCex(xcfa, status.asUnsafe());
				}
			} else {
				System.exit(-1);
			}


			sw.stop();
			System.out.println(sw.elapsed(TimeUnit.MILLISECONDS) + " ms");
		} catch (final Throwable ex) {
			ex.printStackTrace();
		}
	}

//	private void writeStatistics(CFA cfa) {
//		File statistics = new File(statisticsfile);
//		BufferedWriter bw = null;
//		try {
//			bw = new BufferedWriter(new FileWriter(statistics));
//
//			bw.write("CFA-data varCount " + cfa.getVars().size() + System.lineSeparator());
//			bw.write("CFA-data locCount " + cfa.getLocs().size() + System.lineSeparator());
//
//			bw.write("Configuration: ");
//			bw.write(System.lineSeparator());
//			bw.write("Arithmetic: " + (ArchitectureConfig.arithmetic==ArchitectureConfig.ArithmeticType.bitvector? "bitvector" : "integer"));
//			bw.write(System.lineSeparator());
//			bw.write("Domain: " + domain);
//			bw.write(System.lineSeparator());
//			bw.write("Refinement: " + refinement);
//			bw.write(System.lineSeparator());
//			bw.write("Precision granularity: " + precGranularity);
//			bw.write(System.lineSeparator());
//			bw.write("Search: " + search);
//			bw.write(System.lineSeparator());
//			bw.write("Predicate splitting: " + predSplit);
//			bw.write(System.lineSeparator());
//			bw.write("Encoding: " + encoding);
//			bw.write(System.lineSeparator());
//			bw.write("maxEnum: " + maxEnum);
//			bw.write(System.lineSeparator());
//			bw.write("initPrec: " + initPrec);
//			bw.write(System.lineSeparator());
//			bw.write("pruneStrategy: " + pruneStrategy);
//			bw.write(System.lineSeparator());
//
//			bw.close();
//		} catch (IOException e) {
//			e.printStackTrace();
//		}
//	}

	private XcfaConfig<?, ?, ?> buildConfiguration(XCFA xcfa) throws Exception {
		if(ArchitectureConfig.arithmetic == ArchitectureConfig.ArithmeticType.bitvector) {
			return buildBitvectorConfiguration(xcfa);
		}
		return buildIntegerConfiguration(xcfa);
	}

	private XcfaConfig<?, ?, ?> buildIntegerConfiguration(final XCFA xcfa) throws Exception {
		try {
			return new XcfaConfigBuilder(domain, refinement, Z3SolverFactory.getInstance(), algorithm)
					.search(search)
					.predSplit(predSplit).maxEnum(maxEnum).initPrec(initPrec)
					.pruneStrategy(pruneStrategy).logger(new ConsoleLogger(logLevel)).build(xcfa);

		} catch (final Exception ex) {
			throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
		}
	}

	private XcfaConfig<?, ?, ?> buildBitvectorConfiguration(final XCFA xcfa) throws Exception {
		try {
			return new XcfaConfigBuilder(domain, refinement, Z3SolverFactory.getInstance(), algorithm)
					.search(search)
					.predSplit(predSplit).maxEnum(maxEnum).initPrec(initPrec)
					.pruneStrategy(pruneStrategy).logger(new ConsoleLogger(logLevel)).build(xcfa);

		} catch (final Exception ex) {
			throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
		}
	}

	private SafetyResult<?, ?> check(XcfaConfig<?, ?, ?> configuration) throws Exception {
		try {
			return configuration.check();
		} catch (final NotSolvableException exception) {
			System.err.println("Configuration failed (stuck)");
			System.exit(-42); // TODO here for benchexec reasons; tool info should be changed instead
			throw exception;
		} catch (final Exception ex) {
			String message = ex.getMessage() == null ? "(no message)" : ex.getMessage();
			throw new Exception("Error while running algorithm: " + ex.getClass().getSimpleName() + " " + message, ex);
		}
	}

//	private SafetyResult<?, ?> check(XcfaConfig<?, ?, ?> configuration) throws Exception {
//		try {
//			return configuration.check();
//		} catch (final NotSolvableException exception) {
//			System.err.println("Configuration failed (stuck)");
//			System.exit(-42); // TODO here for benchexec reasons; tool info should be changed instead
//			throw exception;
//		} catch (final Exception ex) {
//			String message = ex.getMessage() == null ? "(no message)" : ex.getMessage();
//			throw new Exception("Error while running algorithm: " + ex.getClass().getSimpleName() + " " + message, ex);
//		}
//	}


	private void writeCex(final SafetyResult.Unsafe<?, ?> status) throws FileNotFoundException {
		@SuppressWarnings("unchecked") final Trace<CfaState<?>, CfaAction> trace = (Trace<CfaState<?>, CfaAction>) status.getTrace();
		final Trace<CfaState<ExplState>, CfaAction> concrTrace = CfaTraceConcretizer.concretize(trace, Z3SolverFactory.getInstance());

		if(cexfile!=null) {
			final File file = new File(cexfile);
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
		Graph witnessGraph = XcfaTraceToWitness.buildWitness(concrTrace);
		if(witnessfile!=null) {
			final File file = new File(witnessfile);
			// TODO handle more input flags to get the parameters instead of hardcoding them
			// TODO make WitnessWriter singleton
			WitnessWriter ww = WitnessWriter.createViolationWitnessWriter(model.getAbsolutePath(), "CHECK( init(main()), LTL(G ! call(reach_error())) )", false);
			try {
				ww.writeFile(witnessGraph, witnessfile);
			} catch (FileNotFoundException e) {
				e.printStackTrace();
			}
		}
		if(dotwitnessfile!=null) {
			WitnessGraphvizWriter.getInstance().writeFile(witnessGraph, dotwitnessfile);
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
		final File file = new File(highlighted);
		try (PrintWriter printWriter = new PrintWriter(file)) {
			printWriter.write(xcfa.toDot(cexLocations, cexEdges));
		}
	}
}
