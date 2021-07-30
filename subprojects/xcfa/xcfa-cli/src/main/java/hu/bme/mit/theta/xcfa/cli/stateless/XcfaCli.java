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
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.cfa.analysis.CfaTraceConcretizer;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfig;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.common.CliUtils;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.WitnessGraphvizWriter;
import hu.bme.mit.theta.common.visualization.writer.WitnessWriter;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.XcfaAnalysis;
import hu.bme.mit.theta.xcfa.analysis.XcfaTraceToWitness;
import hu.bme.mit.theta.xcfa.analysis.weakmemory.bounded.BoundedMultithreadedAnalysis;
import hu.bme.mit.theta.xcfa.dsl.gen.CLexer;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.passes.XcfaPassManager;
import hu.bme.mit.theta.xcfa.passes.procedurepass.GlobalVarsToStoreLoad;
import hu.bme.mit.theta.xcfa.passes.procedurepass.OneStmtPerEdgePass;
import hu.bme.mit.theta.xcfa.transformation.ArchitectureConfig;
import hu.bme.mit.theta.xcfa.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.xcfa.transformation.model.statements.CStatement;
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

	@Parameter(names = "--arithmetic-type", description = "Arithmetic type to use when building an XCFA")
	ArchitectureConfig.ArithmeticType arithmeticType = ArchitectureConfig.ArithmeticType.efficient;

	@Parameter(names = "--print-cfa", description = "Print CFA and exit.")
	boolean printcfa;

	@Parameter(names = "--timeout", description = "Seconds until timeout (not precise)")
	Long timeS = Long.MAX_VALUE;

	@Parameter(names = "--version", description = "Display version", help = true)
	boolean versionInfo = false;

	@Parameter(names = "--gui", description = "Show GUI")
	boolean showGui = false;

	@Parameter(names = "--benchmark-parsing", description = "Run parsing tasks only")
	boolean parsing = false;

	@Parameter(names = "--load-store", description = "Map global memory accesses to loads and stores")
	boolean loadStore = false;

	@Parameter(names = "--strict-stmtlist", description = "Exactly one statement per edge")
	boolean oneStmt = false;

	@Parameter(names = "--loglevel", description = "Detailedness of logging")
	Logger.Level logLevel = Logger.Level.SUBSTEP;

	@Parameter(names = "--domain", description = "Abstract domain")
	CfaConfigBuilder.Domain domain = CfaConfigBuilder.Domain.PRED_CART;

	@Parameter(names = "--refinement", description = "Refinement strategy")
	CfaConfigBuilder.Refinement refinement = CfaConfigBuilder.Refinement.BW_BIN_ITP;

	@Parameter(names = "--search", description = "Search strategy")
	CfaConfigBuilder.Search search = CfaConfigBuilder.Search.ERR;

	@Parameter(names = "--predsplit", description = "Predicate splitting (for predicate abstraction)")
	CfaConfigBuilder.PredSplit predSplit = CfaConfigBuilder.PredSplit.WHOLE;

	@Parameter(names = "--precgranularity", description = "Precision granularity")
	CfaConfigBuilder.PrecGranularity precGranularity = CfaConfigBuilder.PrecGranularity.GLOBAL;

	@Parameter(names = "--encoding", description = "Block encoding")
	CfaConfigBuilder.Encoding encoding = CfaConfigBuilder.Encoding.LBE;

	@Parameter(names = "--maxenum", description = "Maximal number of explicitly enumerated successors (0: unlimited)")
	Integer maxEnum = 10;

	@Parameter(names = "--initprec", description = "Initial precision of abstraction")
	CfaConfigBuilder.InitPrec initPrec = CfaConfigBuilder.InitPrec.EMPTY;

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

		try {
			if(outputResults) {
				File resultsDir = new File(model + "-" + LocalDateTime.now().toString() + "-results");
				System.out.println(resultsDir);
				boolean bool = resultsDir.mkdir();
				if(!bool){
					throw new RuntimeException("Couldn't create results directory");
				}

				String basicFileName = resultsDir + "/" + model.getName();
				System.out.println(basicFileName);
				printxcfa = basicFileName + ".xcfa";
				printcfa = true;
				cexfile = basicFileName + ".cex";
				witnessfile = basicFileName + ".witness.graphml";
				dotwitnessfile = basicFileName + ".witness.dot";
				highlighted = basicFileName + ".highlighted.xcfa";
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
			Object built = program.build(null);
			checkState(built instanceof XCFA, "Program is not an XCFA");
			XCFA xcfa = (XCFA) built;

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

			if(showGui) {
				new XcfaGui(xcfa);
				return;
			}

			if (printxcfa!=null) {
				File xcfafile = new File(printxcfa);
				try (BufferedWriter bw = new BufferedWriter(new FileWriter(xcfafile))) {
					bw.write(xcfa.toDot());
				}
			}
			if (printcfa) {
				CFA cfa = xcfa.createCFA();
				File cfafile = new File(model.getAbsolutePath() + ".cfa");
				try (BufferedWriter bw = new BufferedWriter(new FileWriter(cfafile))) {
					bw.write(cfa.toString());
				}
			}


			CFA cfa;
			try {
				cfa = xcfa.createCFA();
			} catch(IllegalStateException e) {
				System.out.println("XCFA not compatible with CFA, using multithreaded analyses.");
				cfa = null;
			}
			if(cfa != null) {
				final CfaConfig<?, ?, ?> configuration = buildConfiguration(cfa, cfa.getErrorLoc().get());
				final SafetyResult<?, ?> status = check(configuration);

				if(statisticsfile!=null) {
					File statistics = new File(statisticsfile);
					BufferedWriter bw = new BufferedWriter(new FileWriter(statistics));
					bw.write("input file name: " + model + System.lineSeparator());
					bw.write("CFA-data varCount " + cfa.getVars().size() + System.lineSeparator());
					bw.write("CFA-data locCount " + cfa.getLocs().size() + System.lineSeparator());

					bw.close();
				}
				if (status.isUnsafe() && cexfile != null) {
					writeCex(status.asUnsafe());
				}
				if (status.isUnsafe() && highlighted != null) {
					writeXcfaWithCex(xcfa, status.asUnsafe());
				}
			} else {
				BoundedMultithreadedAnalysis parametricAnalysis = XcfaAnalysis.createParametricAnalysis(xcfa);
			}


			sw.stop();
			System.out.println(sw.elapsed(TimeUnit.MILLISECONDS) + " ms");
		} catch (final Throwable ex) {
			ex.printStackTrace();
		}
	}

	private CfaConfig<?, ?, ?> buildConfiguration(final CFA cfa, final CFA.Loc errLoc) throws Exception {
		try {
			return new CfaConfigBuilder(CfaConfigBuilder.Domain.PRED_CART, CfaConfigBuilder.Refinement.BW_BIN_ITP, Z3SolverFactory.getInstance())
					.precGranularity(CfaConfigBuilder.PrecGranularity.GLOBAL).search(CfaConfigBuilder.Search.ERR)
					.predSplit(CfaConfigBuilder.PredSplit.WHOLE).encoding(CfaConfigBuilder.Encoding.LBE).maxEnum(1).initPrec(CfaConfigBuilder.InitPrec.EMPTY)
					.pruneStrategy(PruneStrategy.LAZY).logger(new ConsoleLogger(logLevel)).build(cfa, errLoc);

		} catch (final Exception ex) {
			throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
		}
	}

	private SafetyResult<?, ?> check(CfaConfig<?, ?, ?> configuration) throws Exception {
		try {
			return configuration.check();
		} catch (final Exception ex) {
			String message = ex.getMessage() == null ? "(no message)" : ex.getMessage();
			throw new Exception("Error while running algorithm: " + ex.getClass().getSimpleName() + " " + message, ex);
		}
	}

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
				Set<Object> xcfaEdges = XcfaMetadata.lookupMetadata("cfaEdge", edge);
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
