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
import hu.bme.mit.theta.cfa.analysis.config.CfaConfig;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.cfa.dsl.CfaWriter;
import hu.bme.mit.theta.common.CliUtils;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.WitnessGraphvizWriter;
import hu.bme.mit.theta.common.visualization.writer.WitnessWriter;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.CStmtCounter;
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xcfa.algorithmselection.MaxEnumAnalyzer;
import hu.bme.mit.theta.xcfa.algorithmselection.NoNewCexException;
import hu.bme.mit.theta.xcfa.algorithmselection.NotSolvableException;
import hu.bme.mit.theta.xcfa.algorithmselection.PortfolioHandler;
import hu.bme.mit.theta.xcfa.algorithmselection.PortfolioNotSolvableThrower;
import hu.bme.mit.theta.xcfa.analysis.XcfaAnalysis;
import hu.bme.mit.theta.xcfa.analysis.XcfaTraceToWitness;
import hu.bme.mit.theta.xcfa.analysis.weakmemory.bounded.BoundedMultithreadedAnalysis;
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
import java.time.LocalDateTime;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

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

	String cfafile = null;

	// @Parameter(names = "--print-xcfa", description = "Print XCFA (as a dotfile) and exit.")
	String printxcfa = null;

	@Parameter(names = "--no-bitvectors", description = "Stops the verification if the usage of bitvector arithmetics would be required for the task")
	boolean noBitvectors = false;

	@Parameter(names = "--cfa-input-statistics")
	boolean cfaInputStatistics = false;

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

	@Parameter(names = "--gui", description = "Show GUI")
	boolean showGui = false;

	@Parameter(names = "--bmc", description = "Run BMC pre-check")
	boolean runbmc = false;

	@Parameter(names = "--benchmark-parsing", description = "Run parsing tasks only")
	boolean parsing = false;

	@Parameter(names = "--load-store", description = "Map global memory accesses to loads and stores")
	boolean loadStore = false;

	@Parameter(names = "--strict-stmtlist", description = "Exactly one statement per edge")
	boolean oneStmt = false;

	@Parameter(names = "--loglevel", description = "Detailedness of logging")
	Logger.Level logLevel = Logger.Level.MAINSTEP;

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
				cfafile = basicFileName + ".cfa";
				cexfile = basicFileName + ".cex";
				witnessfile = basicFileName + ".witness.graphml";
				dotwitnessfile = basicFileName + ".witness.dot";
				highlighted = basicFileName + ".highlighted.xcfa";
				statisticsfile = basicFileName + ".statistics.txt";
			} else if(printcfa) {
				File resultsDir = new File(model + "-" + LocalDateTime.now().toString() + "-results");
				boolean bool = resultsDir.mkdir();
				if(!bool){
					throw new RuntimeException("Couldn't create results directory");
				}

				String basicFileName = resultsDir + "/" + model.getName();
				statisticsfile = basicFileName + ".statistics.txt";
				cfafile = basicFileName + ".cfa";
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
				maxEnum = MaxEnumAnalyzer.instance.estimateMaxEnum().intValue();
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

			if (printcfa || outputResults) {
				CFA cfa = xcfa.createCFA();
				try (FileOutputStream filestream = new FileOutputStream(cfafile)) {
					CfaWriter.write(cfa, filestream);
				}
				writeStatistics(cfa);

				// cfa data only in csv format
				try	(BufferedWriter bw = new BufferedWriter(new FileWriter(cfafile+".csv"))) {
					bw.write(model.getName() + "\t");
					bw.write(cfa.getVars().size() + "\t"); // vars
					bw.write(cfa.getEdges().stream().filter(edge -> edge.getStmt() instanceof HavocStmt).count() + "\t"); // havocs
					bw.write(cfa.getLocs().size() + "\t"); // locs
					bw.write(cfa.getEdges().size() + "\t"); // edges
					bw.write(cfa.getEdges().stream().
							filter(edge -> edge.getStmt().equals(SkipStmt.getInstance())).count() + "\t"); // skip edges
					bw.write(cfa.getEdges().stream().filter(edge-> edge.getStmt() instanceof AssumeStmt).count() + "\t"); // assumes
					bw.write(cfa.getEdges().stream().filter(edge-> edge.getStmt() instanceof AssignStmt).count() + "\t"); // assign

					List<Integer> rs = cfa.getLocs().stream().map(loc -> loc.getOutEdges().size()).collect(Collectors.toList());
					int avgGrade = 0;
					for(Integer r : rs) {
						avgGrade += r;
					}
					avgGrade /= cfa.getLocs().size()-1; // final loc does not count and there must be one final loc
					bw.write(avgGrade + "\t"); // average grades of outgoing edges

					long highInGradeLocs = cfa.getLocs().stream().filter(loc -> loc.getInEdges().size()>1).count();
					long highOutGradeLocs = cfa.getLocs().stream().filter(loc -> loc.getOutEdges().size()>1).count();
					bw.write(highOutGradeLocs + "\t"); // num of locations with more than one out-edges
					bw.write(highInGradeLocs + "\t"); // num of locations with more than one in-edges

					int maxOutGrade = cfa.getLocs().stream().map(loc -> loc.getOutEdges().size()).max(Integer::compareTo).get();
					int minOutGrade = cfa.getLocs().stream().filter(loc -> !loc.equals(cfa.getFinalLoc().get()) && !loc.equals(cfa.getErrorLoc().get())).map(loc -> loc.getOutEdges().size()).min(Integer::compareTo).get();
					bw.write(maxOutGrade + "\t"); // max out grade on a single location
					bw.write(minOutGrade + "\t"); // max out grade on a single location (except error/final)

					int maxInGrade = cfa.getLocs().stream().map(loc -> loc.getInEdges().size()).max(Integer::compareTo).get();
					int minInGrade = cfa.getLocs().stream().filter(loc -> !loc.equals(cfa.getInitLoc())).map(loc -> loc.getInEdges().size()).min(Integer::compareTo).get();
					bw.write(maxInGrade + "\t"); // max in grade on a single location
					bw.write(minInGrade + "\t"); // min in grade on a single location  (except init)

					bw.write((cfa.getEdges().size() - cfa.getLocs().size() + 2) + "\t"); // cyclomatic complexity
					bw.write(CStmtCounter.getForLoops() + "\t"); // for loops
					bw.write(CStmtCounter.getWhileLoops() + "\t"); // while loops
					bw.write(CStmtCounter.getBranches() + "\n"); // branches

					bw.close();
				}
				if(printcfa) return;
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
			if(cfa != null) {
				final SafetyResult<?, ?> status;
				if(!portfolio) {
					final CfaConfig<?, ?, ?> configuration = buildConfiguration(cfa, cfa.getErrorLoc().get());
					CegarChecker.setNotSolvableThrower(new PortfolioNotSolvableThrower(false));
					status = check(configuration);
					if(statisticsfile!=null) {
						writeStatistics(cfa);
					}
				} else {
					status = PortfolioHandler.instance.executeAnalysis(cfa, logLevel, statisticsfile);
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

	private void writeStatistics(CFA cfa) {
		File statistics = new File(statisticsfile);
		BufferedWriter bw = null;
		try {
			bw = new BufferedWriter(new FileWriter(statistics));

			bw.write("CFA-data varCount " + cfa.getVars().size() + System.lineSeparator());
			bw.write("CFA-data havocs " + cfa.getEdges().stream().filter(edge -> edge.getStmt() instanceof HavocStmt).count() + "\t"); // havocs
			bw.write("CFA-data locCount " + cfa.getLocs().size() + System.lineSeparator());
			bw.write("CFA-data edgeCount " + cfa.getEdges().size() + System.lineSeparator());
			bw.write("CFA-data skipEdgeCount " + cfa.getEdges().stream().filter(edge -> edge.getStmt().equals(SkipStmt.getInstance())).count() + System.lineSeparator());
			bw.write("CFA-data assumeStmts"+cfa.getEdges().stream().filter(edge-> edge.getStmt() instanceof AssumeStmt).count() + "\t"); // assumes
			bw.write("CFA-data assignStmts"+cfa.getEdges().stream().filter(edge-> edge.getStmt() instanceof AssignStmt).count() + "\t"); // assign
			bw.write("CFA-data cyclomatic complexity " + (cfa.getEdges().size() - cfa.getLocs().size() + 2) + System.lineSeparator());
			List<Integer> rs = cfa.getLocs().stream().map(loc -> loc.getOutEdges().size()).collect(Collectors.toList());
			int avgGrade = 0;
			for(Integer r : rs) {
				avgGrade += r;
			}
			avgGrade /= cfa.getLocs().size();
			bw.write("CFA-data averageOutEdgeGrade" + avgGrade + "\t"); // average grades of outgoing edges
			long highOutGradeLocs = cfa.getLocs().stream().filter(loc -> loc.getOutEdges().size()>1).count();
			long highInGradeLocs = cfa.getLocs().stream().filter(loc -> loc.getInEdges().size()>1).count();

			bw.write("CFA-data locsWithHigherOutGrade" + highOutGradeLocs + "\t"); // num of locations with more than one out-edges
			bw.write("CFA-data locsWithHigherInGrade" + highInGradeLocs + "\t"); // num of locations with more than one in-edges

			int maxOutGrade = cfa.getLocs().stream().map(loc -> loc.getOutEdges().size()).max(Integer::compareTo).get();
			int minOutGrade = cfa.getLocs().stream().filter(loc -> !loc.equals(cfa.getFinalLoc().get()) && !loc.equals(cfa.getErrorLoc().get())).map(loc -> loc.getOutEdges().size()).min(Integer::compareTo).get();
			bw.write("CFA-data maxOutGrade" + maxOutGrade + "\t"); // max out grade on a single location
			bw.write("CFA-data minOutGrade" + minOutGrade + "\t"); // max out grade on a single location (except error/final)

			int maxInGrade = cfa.getLocs().stream().map(loc -> loc.getInEdges().size()).max(Integer::compareTo).get();
			int minInGrade = cfa.getLocs().stream().filter(loc -> !loc.equals(cfa.getInitLoc())).map(loc -> loc.getInEdges().size()).min(Integer::compareTo).get();
			bw.write("CFA-data maxInGrade" + maxInGrade + "\t"); // max in grade on a single location
			bw.write("CFA-data minInGrade" + minInGrade + "\t"); // min in grade on a single location  (except init)

			bw.write("C-data forLoops"+CStmtCounter.getForLoops() + "\t"); // for loops
			bw.write("C-data whileLoops"+CStmtCounter.getWhileLoops() + "\t"); // while loops
			bw.write("C-data branches"+CStmtCounter.getBranches() + "\n"); // branches

			bw.write("Configuration: ");
			bw.write(System.lineSeparator());
			bw.write("Arithmetic: " + (ArchitectureConfig.arithmetic==ArchitectureConfig.ArithmeticType.bitvector? "bitvector" : "integer"));
			bw.write(System.lineSeparator());
			bw.write("Domain: " + domain);
			bw.write(System.lineSeparator());
			bw.write("Refinement: " + refinement);
			bw.write(System.lineSeparator());
			bw.write("Precision granularity: " + precGranularity);
			bw.write(System.lineSeparator());
			bw.write("Search: " + search);
			bw.write(System.lineSeparator());
			bw.write("Predicate splitting: " + predSplit);
			bw.write(System.lineSeparator());
			bw.write("Encoding: " + encoding);
			bw.write(System.lineSeparator());
			bw.write("maxEnum: " + maxEnum);
			bw.write(System.lineSeparator());
			bw.write("initPrec: " + initPrec);
			bw.write(System.lineSeparator());
			bw.write("pruneStrategy: " + pruneStrategy);
			bw.write(System.lineSeparator());

			bw.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private CfaConfig<?, ?, ?> buildConfiguration(CFA cfa, CFA.Loc loc) throws Exception {
		if(ArchitectureConfig.arithmetic == ArchitectureConfig.ArithmeticType.bitvector) {
			return buildBitvectorConfiguration(cfa, loc);
		}
		return buildIntegerConfiguration(cfa, loc);
	}

	private CfaConfig<?, ?, ?> buildIntegerConfiguration(final CFA cfa, final CFA.Loc errLoc) throws Exception {
		try {
			return new CfaConfigBuilder(domain, refinement, Z3SolverFactory.getInstance())
					.precGranularity(precGranularity).search(search)
					.predSplit(predSplit).encoding(encoding).maxEnum(maxEnum).initPrec(initPrec)
					.pruneStrategy(pruneStrategy).logger(new ConsoleLogger(logLevel)).build(cfa, errLoc);

		} catch (final Exception ex) {
			throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
		}
	}

	private CfaConfig<?, ?, ?> buildBitvectorConfiguration(final CFA cfa, final CFA.Loc errLoc) throws Exception {
		// TODO for benchmarks
		if(noBitvectors) {
			System.err.println("Bitvectors required, stopping verification");
			System.exit(-50); // TODO here for benchexec reasons
		}

		try {
			return new CfaConfigBuilder(domain, refinement, Z3SolverFactory.getInstance())
					.precGranularity(precGranularity).search(search)
					.predSplit(predSplit).encoding(encoding).maxEnum(maxEnum).initPrec(initPrec)
					.pruneStrategy(pruneStrategy).logger(new ConsoleLogger(logLevel)).build(cfa, errLoc);

		} catch (final Exception ex) {
			throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
		}
	}

	private SafetyResult<?, ?> check(CfaConfig<?, ?, ?> configuration) throws Exception {
		try {
			return configuration.check();
		} catch (final NotSolvableException exception) {
			System.err.println("Configuration failed (stuck)");
			System.exit(-42); // TODO here for benchexec reasons; tool info should be changed instead
			throw exception;
		} catch (final NoNewCexException exception) {
			System.err.println("Configuration failed (no new cex found)");
			System.exit(-30); // TODO here for benchexec reasons; tool info should be changed instead
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
