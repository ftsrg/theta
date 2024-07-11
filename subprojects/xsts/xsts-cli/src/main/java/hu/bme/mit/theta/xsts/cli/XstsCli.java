/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xsts.cli;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Preconditions;
import com.google.common.base.Stopwatch;
import com.koloboke.collect.set.hash.HashObjSets;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.impl.RecursiveIntObjMapViews;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarStatistics;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddAnalysisStatistics;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddCex;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddWitness;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.utils.MddNodeVisualizer;
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
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.BfsProvider;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.GeneralizedSaturationProvider;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.SimpleSaturationProvider;
import hu.bme.mit.theta.frontend.petrinet.analysis.PtNetDependency2Gxl;
import hu.bme.mit.theta.frontend.petrinet.analysis.PtNetSystem;
import hu.bme.mit.theta.frontend.petrinet.analysis.VariableOrderingFactory;
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet;
import hu.bme.mit.theta.frontend.petrinet.model.Place;
import hu.bme.mit.theta.frontend.petrinet.pnml.PetriNetParser;
import hu.bme.mit.theta.frontend.petrinet.pnml.PnmlParseException;
import hu.bme.mit.theta.frontend.petrinet.pnml.XMLPnmlToPetrinet;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.solver.z3legacy.Z3SolverManager;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.XstsAction;
import hu.bme.mit.theta.xsts.analysis.XstsState;
import hu.bme.mit.theta.xsts.analysis.concretizer.XstsStateSequence;
import hu.bme.mit.theta.xsts.analysis.concretizer.XstsTraceConcretizerUtil;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfig;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.Algorithm;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.AutoExpl;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.Domain;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.InitPrec;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.OptimizeStmts;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.PredSplit;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.Refinement;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.Search;
import hu.bme.mit.theta.xsts.analysis.mdd.XstsMddChecker;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;
import hu.bme.mit.theta.frontend.petrinet.xsts.PetriNetToXSTS;

import javax.imageio.ImageIO;
import java.awt.image.BufferedImage;
import java.io.*;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Stream;

import static hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder.IterationStrategy;

public class XstsCli {

    private static final String JAR_NAME = "theta-xsts-cli.jar";
    private final String[] args;
    private final TableWriter writer;

    //////////// CONFIGURATION OPTIONS BEGIN ////////////

    //////////// input task ////////////

    @Parameter(names = {"--model"}, description = "Path of the input model (XSTS or Pnml)", required = true)
    String model;

    @Parameter(names = {"--property"}, description = "Input property as a string or a file (*.prop)")
    String property;

    @Parameter(names = "--id", description = "Id of the input model")
    String id = "";

    @Parameter(names = "--ordering", description = "Path of the input variable ordering")
    String orderingPath;

    //////////// algorithm selection ////////////

    @Parameter(names = {"--algorithm"}, description = "Algorithm selection")
    Algorithm algorithm = Algorithm.CEGAR;

    //////////// output data and statistics ////////////

    @Parameter(names = {"--loglevel"}, description = "Detailedness of logging")
    Logger.Level logLevel = Logger.Level.SUBSTEP;

    @Parameter(names = {"--benchmark"}, description = "Benchmark mode (only print metrics)")
    Boolean benchmarkMode = false;

    @Parameter(names = {"--cex"}, description = "Write concrete counterexample to a file")
    String cexfile = null;

    @Parameter(names = {"--header"}, description = "Print only a header (for benchmarks)", help = true)
    boolean headerOnly = false;

    @Parameter(names = "--metrics", description = "Print metrics about the XSTS without running the algorithm")
    boolean metrics = false;

    @Parameter(names = "--stacktrace", description = "Print full stack trace in case of exception")
    boolean stacktrace = false;

    @Parameter(names = "--version", description = "Display version", help = true)
    boolean versionInfo = false;

    @Parameter(names = {"--visualize"}, description = "Write proof or counterexample to file in dot format")
    String dotfile = null;

    //////////// CEGAR configuration options ////////////

    @Parameter(names = {"--domain"}, description = "Abstract domain")
    Domain domain = Domain.PRED_CART;

    @Parameter(names = {"--refinement"}, description = "Refinement strategy")
    Refinement refinement = Refinement.SEQ_ITP;

    @Parameter(names = {"--search"}, description = "Search strategy")
    Search search = Search.BFS;

    @Parameter(names = {"--refinement-solver"}, description = "Refinement solver name")
    String refinementSolver = "Z3";

    @Parameter(names = {"--abstraction-solver"}, description = "Abstraction solver name")
    String abstractionSolver = "Z3";

    @Parameter(names = {"--smt-home"}, description = "The path of the solver registry")
    String solverHome = SmtLibSolverManager.HOME.toAbsolutePath().toString();

    @Parameter(names = "--no-stuck-check")
    boolean noStuckCheck = false;

    @Parameter(names = {"--predsplit"}, description = "Predicate splitting")
    PredSplit predSplit = PredSplit.WHOLE;

    @Parameter(names = {"--initialmarking"}, description = "Initial marking of the Petri net")
    String initialMarking = "";

    @Parameter(names = "--maxenum", description = "Maximal number of explicitly enumerated successors (0: unlimited)")
    Integer maxEnum = 0;

    @Parameter(names = "--autoexpl", description = "Predicate to explicit switching strategy")
    AutoExpl autoExpl = AutoExpl.NEWOPERANDS;

    @Parameter(names = {"--initprec"}, description = "Initial precision")
    InitPrec initPrec = InitPrec.EMPTY;

    @Parameter(names = "--prunestrategy", description = "Strategy for pruning the ARG after refinement")
    PruneStrategy pruneStrategy = PruneStrategy.LAZY;

    @Parameter(names = "--optimizestmts", description = "Turn statement optimization on or off")
    OptimizeStmts optimizeStmts = OptimizeStmts.ON;

    //////////// symbolic configuration options ////////////

    @Parameter(names = "--iterationStrategy", description = "The state space generation algorithm to use (BFS, Saturation or " +
            "GeneralizedSaturation)")
    IterationStrategy iterationStrategy = IterationStrategy.GSAT;

    //////////// petri net output options ////////////

    @Parameter(names = "--depgxl", description =
            "Generate GXL representation of (extended) dependency graph for variable ordering in the" +
                    " specified file")
    String depGxl;

    @Parameter(names = "--depgxlgsat", description =
            "Generate GXL representation of (extended) dependency graph for variable ordering in the" +
                    " specified file")
    String depGxlGsat;

    @Parameter(names = "--depmat",
            description = "Generate dependency matrix from the model as a CSV file to the specified path")
    String depMat;

    @Parameter(names = "--depmatpng",
            description = "Generate dependency matrix from the model as a PNG file to the specified path")
    String depMatPng;

    //////////// CONFIGURATION OPTIONS END ////////////

    private Logger logger;

    public XstsCli(final String[] args) {
        this.args = args;
        writer = new BasicTableWriter(System.out, ",", "\"", "\"");
    }

    public static void main(final String[] args) {
        final XstsCli mainApp = new XstsCli(args);
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
            printHeader(algorithm);
            return;
        }

        if (versionInfo) {
            CliUtils.printVersion(System.out);
            return;
        }

        try {

            if (algorithm == Algorithm.CEGAR) {
                runCegarAnalysis();
            } else if (algorithm == Algorithm.MDD) {
                if (model.endsWith(".pnml")) {
                    runPetrinetMddAnalysis();
                } else {
                    runXstsMddAnalysis();
                }
            } else {
                throw new UnsupportedOperationException("Algorithm not supported: " + algorithm);
            }

        } catch (final Throwable ex) {
            printError(ex);
            System.exit(1);
        }
    }

    private void runCegarAnalysis() throws Exception {
        final Stopwatch sw = Stopwatch.createStarted();

        final XSTS xsts = loadXSTSModel();

        if (metrics) {
            XstsMetrics.printMetrics(logger, xsts);
            return;
        }

        final XstsConfig<?, ?, ?> configuration = buildConfiguration(xsts);
        final SafetyResult<? extends ARG<?, ?>, ? extends Trace<? extends State, ? extends Action>> status = check(configuration);
        sw.stop();
        printCegarResult(status, xsts, sw.elapsed(TimeUnit.MILLISECONDS));
        if (status.isUnsafe() && cexfile != null) {
            writeCex(status.asUnsafe(), xsts);
        }
        if (dotfile != null) {
            writeVisualStatus(status, dotfile);
        }
    }

    private void runXstsMddAnalysis() throws Exception {
        final Stopwatch sw = Stopwatch.createStarted();

        final XSTS xsts = loadXSTSModel();

        if (metrics) {
            XstsMetrics.printMetrics(logger, xsts);
            return;
        }

        final MddChecker.IterationStrategy mddIterationStrategy;
        switch (iterationStrategy) {
            case BFS -> mddIterationStrategy = MddChecker.IterationStrategy.BFS;
            case SAT -> mddIterationStrategy = MddChecker.IterationStrategy.SAT;
            case GSAT -> mddIterationStrategy = MddChecker.IterationStrategy.GSAT;
            default ->
                    throw new UnsupportedOperationException("Iteration strategy not supported: " + iterationStrategy);
        }

        final SafetyResult<MddWitness, MddCex> status;
        try (var solverPool = new SolverPool(Z3LegacySolverFactory.getInstance())) {
            final XstsMddChecker checker = XstsMddChecker.create(xsts, solverPool, logger, mddIterationStrategy);
            status = checker.check(null);
            sw.stop();
        }

        printSymbolicResult(status, xsts, sw.elapsed(TimeUnit.MILLISECONDS));
        if (dotfile != null) {
            writeXstsMddVisualStatus(status, dotfile);
        }
    }

    private void runPetrinetMddAnalysis() throws Exception {
        final Stopwatch totalTimer = Stopwatch.createStarted();

        final List<PetriNet> petriNets = loadPetriNetModel();
        final List<Place> ordering = loadOrdering(petriNets);

        final PtNetSystem system = new PtNetSystem(petriNets.get(0), ordering);

        if (depGxl != null) {
            createDepGxl(system);
        }

        if (depGxlGsat != null) {
            createDepGxlGSat(system);
        }

        if (depMat != null) {
            createDepMat(system);
        }

        if (depMatPng != null) {
            createDepMatPng(system);
        }

        final MddVariableOrder variableOrder = JavaMddFactory.getDefault().createMddVariableOrder(LatticeDefinition.forSets());
        ordering.forEach(p -> variableOrder.createOnTop(MddVariableDescriptor.create(p)));

        final Stopwatch ssgTimer = Stopwatch.createStarted();

        switch (iterationStrategy) {
            // TODO: NODE COUNT IN MDD!!!!
            case BFS: {
                final BfsProvider bfs = new BfsProvider(variableOrder);

                final MddHandle stateSpace = bfs.compute(system.getInitializer(),
                        system.getTransitions(),
                        variableOrder.getDefaultSetSignature().getTopVariableHandle()
                );

                ssgTimer.stop();
                totalTimer.stop();

                printSymbolicResult(writer,
                        variableOrder,
                        system,
                        stateSpace,
                        bfs,
                        totalTimer.elapsed(TimeUnit.MICROSECONDS),
                        ssgTimer.elapsed(TimeUnit.MICROSECONDS)
                );
            }
            break;
            case SAT: {
                final SimpleSaturationProvider ss = new SimpleSaturationProvider(variableOrder);

                final MddHandle stateSpace = ss.compute(system.getInitializer(),
                        system.getTransitions(),
                        variableOrder.getDefaultSetSignature().getTopVariableHandle()
                );

                ssgTimer.stop();
                totalTimer.stop();

                printSymbolicResult(writer,
                        variableOrder,
                        system,
                        stateSpace,
                        ss,
                        totalTimer.elapsed(TimeUnit.MICROSECONDS),
                        ssgTimer.elapsed(TimeUnit.MICROSECONDS)
                );
            }
            break;
            case GSAT: {
                final GeneralizedSaturationProvider gs = new GeneralizedSaturationProvider(variableOrder);

                final MddHandle stateSpace = gs.compute(system.getInitializer(),
                        system.getTransitions(),
                        variableOrder.getDefaultSetSignature().getTopVariableHandle()
                );

                ssgTimer.stop();
                totalTimer.stop();

                printSymbolicResult(writer,
                        variableOrder,
                        system,
                        stateSpace,
                        gs,
                        totalTimer.elapsed(TimeUnit.MICROSECONDS),
                        ssgTimer.elapsed(TimeUnit.MICROSECONDS)
                );
            }
            break;

        }
    }

    private SafetyResult<? extends ARG<?, ?>, ? extends Trace<? extends State, ? extends Action>> check(XstsConfig<?, ?, ?> configuration) throws Exception {
        try {
            return configuration.check();
        } catch (final Exception ex) {
            String message = ex.getMessage() == null ? "(no message)" : ex.getMessage();
            throw new Exception("Error while running algorithm: " + ex.getClass().getSimpleName() + " " + message, ex);
        }
    }

    private void printHeader(Algorithm algorithm) {
        if (algorithm == Algorithm.CEGAR) {
            printCegarHeader();
        } else {
            printSymbolicHeader();
        }
    }

    private void printCegarHeader() {
        Stream.of("Result", "TimeMs", "AlgoTimeMs", "AbsTimeMs", "RefTimeMs", "Iterations",
                "ArgSize", "ArgDepth", "ArgMeanBranchFactor", "CexLen", "Vars").forEach(writer::cell);
        writer.newRow();
    }

    // TODO: NODE COUNT IN MDD!!!!
    private void printSymbolicHeader() {
        switch (iterationStrategy) {
            case BFS:
                writer.cell("id");
                writer.cell("modelPath");
                writer.cell("modelName");
                writer.cell("stateSpaceSize");
                writer.cell("finalMddSize");
                writer.cell("totalTimeUs");
                writer.cell("ssgTimeUs");
                writer.cell("nodeCount");
                writer.cell("unionCacheSize");
                writer.cell("unionQueryCount");
                writer.cell("unionHitCount");
                writer.cell("relProdCacheSize");
                writer.cell("relProdQueryCount");
                writer.cell("relProdHitCount");
                writer.newRow();
                break;
            case SAT:
            case GSAT:
                writer.cell("id");
                writer.cell("modelPath");
                writer.cell("modelName");
                writer.cell("stateSpaceSize");
                writer.cell("finalMddSize");
                writer.cell("totalTimeUs");
                writer.cell("ssgTimeUs");
                writer.cell("nodeCount");
                writer.cell("unionCacheSize");
                writer.cell("unionQueryCount");
                writer.cell("unionHitCount");
                writer.cell("saturateCacheSize");
                writer.cell("saturateQueryCount");
                writer.cell("saturateHitCount");
                writer.cell("relProdCacheSize");
                writer.cell("relProdQueryCount");
                writer.cell("relProdHitCount");
                writer.cell("saturatedNodeCount");
                writer.newRow();
                break;
        }
    }

    private XSTS loadXSTSModel() throws Exception {
        InputStream propStream = null;
        Preconditions.checkNotNull(property, "No property defined. Did you select the correct algorithm? (Default is CEGAR)");
        try {
            if (property.endsWith(".prop")) propStream = new FileInputStream(property);
            else propStream = new ByteArrayInputStream(("prop { " + property + " }").getBytes());

            if (model.endsWith(".pnml")) {
                final PetriNet petriNet = XMLPnmlToPetrinet.parse(model, initialMarking);
                return PetriNetToXSTS.createXSTS(petriNet, propStream);
            } else {

                try (SequenceInputStream inputStream = new SequenceInputStream(new FileInputStream(model), propStream)) {
                    return XstsDslManager.createXsts(inputStream);
                }
            }

        } catch (Exception ex) {
            throw new Exception("Could not parse XSTS: " + ex.getMessage(), ex);
        } finally {
            if (propStream != null) propStream.close();
        }
    }

    private List<PetriNet> loadPetriNetModel() throws Exception {
        final File pnmlFile = new File(model);
        final List<PetriNet> petriNets;
        try {
            petriNets = PetriNetParser.loadPnml(pnmlFile).parsePTNet();
        } catch (PnmlParseException e) {
            throw new Exception("Invalid PNML: " + e.getMessage());
        } catch (Exception e) {
            throw new Exception("An error occured while loading the modelPath: " + e.getMessage());
        }

        if (petriNets.isEmpty()) {
            throw new Exception("No Petri net found in the PNML document.");
        }

        return petriNets;
    }

    private List<Place> loadOrdering(final List<PetriNet> petriNets) throws Exception {
        final List<Place> ordering;
        if (orderingPath == null) {
            logger.write(Logger.Level.INFO, "[WARNING] No ordering specified, using default order.");
            ordering = new ArrayList<>(petriNets.get(0).getPlaces());
            ordering.sort((p1, p2) -> String.CASE_INSENSITIVE_ORDER.compare(reverseString(p1.getId()),
                    reverseString(p2.getId())
            ));
        } else {
            try {
                ordering = VariableOrderingFactory.fromFile(orderingPath, petriNets.get(0));
            } catch (IOException e) {
                throw new Exception("Error reading ordering file: " + e.getMessage());
            } catch (Exception e) {
                throw new Exception(e.getMessage());
            }
        }
        return ordering;
    }

    private XstsConfig<?, ?, ?> buildConfiguration(final XSTS xsts) throws Exception {
        // set up stopping analysis if it is stuck on same ARGs and precisions
        //if (noStuckCheck) {
        //ArgCexCheckHandler.instance.setArgCexCheck(false, false);
        //} else {
        //ArgCexCheckHandler.instance.setArgCexCheck(true, refinement.equals(Refinement.MULTI_SEQ));
        //        }

        registerAllSolverManagers(solverHome, logger);
        SolverFactory abstractionSolverFactory = SolverManager.resolveSolverFactory(abstractionSolver);
        SolverFactory refinementSolverFactory = SolverManager.resolveSolverFactory(refinementSolver);

        try {
            return new XstsConfigBuilder(domain, refinement, abstractionSolverFactory, refinementSolverFactory)
                    .maxEnum(maxEnum).autoExpl(autoExpl).initPrec(initPrec).pruneStrategy(pruneStrategy)
                    .search(search).predSplit(predSplit).optimizeStmts(optimizeStmts).logger(logger).build(xsts);
        } catch (final Exception ex) {
            throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
        }
    }

    private void printCegarResult(final SafetyResult<? extends ARG<?, ?>, ? extends Trace<?, ?>> status, final XSTS sts, final long totalTimeMs) {
        final CegarStatistics stats = (CegarStatistics)
                status.getStats().orElse(new CegarStatistics(0, 0, 0, 0));
        if (benchmarkMode) {
            writer.cell(status.isSafe());
            writer.cell(totalTimeMs);
            writer.cell(stats.getAlgorithmTimeMs());
            writer.cell(stats.getAbstractorTimeMs());
            writer.cell(stats.getRefinerTimeMs());
            writer.cell(stats.getIterations());
            writer.cell(status.getWitness().size());
            writer.cell(status.getWitness().getDepth());
            writer.cell(status.getWitness().getMeanBranchingFactor());
            if (status.isUnsafe()) {
                writer.cell(status.asUnsafe().getCex().length() + "");
            } else {
                writer.cell("");
            }
            writer.cell(sts.getVars().size());
            writer.newRow();
        }
    }

    private void printSymbolicResult(final SafetyResult<MddWitness, MddCex> status, final XSTS sts, final long totalTimeMs) {
        final MddAnalysisStatistics stats = (MddAnalysisStatistics)
                status.getStats().orElse(new MddAnalysisStatistics(0L, 0L, 0L, 0L, 0L));
        if (benchmarkMode) {
            writer.cell(status.isSafe());
            writer.cell(totalTimeMs);
            writer.cell(status.getWitness().size());
            writer.cell(stats.getViolatingSize());
            writer.cell(stats.getStateSpaceSize());
            writer.cell(stats.getHitCount());
            writer.cell(stats.getQueryCount());
            writer.cell(stats.getCacheSize());
            if (status.isUnsafe()) {
                writer.cell(status.asUnsafe().getCex().length() + "");
            } else {
                writer.cell("");
            }
            writer.cell(sts.getVars().size());
            writer.newRow();
        }
    }

    private void printSymbolicResult(
            TableWriter writer,
            MddVariableOrder variableOrder,
            PtNetSystem system,
            MddHandle result,
            GeneralizedSaturationProvider provider,
            long totalTime,
            long ssgTime
    ) {
        String id = this.id;
        String modelPath = this.model;
        String modelName = system.getName();

        Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(result);
        long nodeCount = variableOrder.getMddGraph().getUniqueTableSize();

        long unionCacheSize = variableOrder.getDefaultUnionProvider().getCacheSize();
        long unionQueryCount = variableOrder.getDefaultUnionProvider().getQueryCount();
        long unionHitCount = variableOrder.getDefaultUnionProvider().getHitCount();

        long saturateCacheSize = provider.getSaturateCache().getCacheSize();
        long saturateQueryCount = provider.getSaturateCache().getQueryCount();
        long saturateHitCount = provider.getSaturateCache().getHitCount();

        long relProdCacheSize = provider.getSaturateCache().getCacheSize();
        long relProdQueryCount = provider.getSaturateCache().getQueryCount();
        long relProdHitCount = provider.getSaturateCache().getHitCount();

        final Set<MddNode> nodes = MddNodeCollector.collectNodes(result);
        long finalMddSize = nodes.size();

        final Set<MddNode> saturatedNodes = provider.getSaturatedNodes();
        long saturatedNodeCount = saturatedNodes.size() + 2;

        writer.cell(id);
        writer.cell(modelPath);
        writer.cell(modelName);
        writer.cell(stateSpaceSize);
        writer.cell(finalMddSize);
        writer.cell(totalTime);
        writer.cell(ssgTime);
        writer.cell(nodeCount);
        writer.cell(unionCacheSize);
        writer.cell(unionQueryCount);
        writer.cell(unionHitCount);
        writer.cell(saturateCacheSize);
        writer.cell(saturateQueryCount);
        writer.cell(saturateHitCount);
        writer.cell(relProdCacheSize);
        writer.cell(relProdQueryCount);
        writer.cell(relProdHitCount);
        writer.cell(saturatedNodeCount);
        writer.newRow();
    }

    private void printSymbolicResult(
            TableWriter writer,
            MddVariableOrder variableOrder,
            PtNetSystem system,
            MddHandle result,
            SimpleSaturationProvider provider,
            long totalTime,
            long ssgTime
    ) {
        String id = this.id;
        String modelPath = this.model;
        String modelName = system.getName();

        Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(result);
        long nodeCount = variableOrder.getMddGraph().getUniqueTableSize();

        long unionCacheSize = variableOrder.getDefaultUnionProvider().getCacheSize();
        long unionQueryCount = variableOrder.getDefaultUnionProvider().getQueryCount();
        long unionHitCount = variableOrder.getDefaultUnionProvider().getHitCount();

        long saturateCacheSize = provider.getSaturateCache().getCacheSize();
        long saturateQueryCount = provider.getSaturateCache().getQueryCount();
        long saturateHitCount = provider.getSaturateCache().getHitCount();

        long relProdCacheSize = provider.getSaturateCache().getCacheSize();
        long relProdQueryCount = provider.getSaturateCache().getQueryCount();
        long relProdHitCount = provider.getSaturateCache().getHitCount();


        final Set<MddNode> nodes = MddNodeCollector.collectNodes(result);
        long finalMddSize = nodes.size();

        final Set<MddNode> saturatedNodes = provider.getSaturatedNodes();
        long saturatedNodeCount = saturatedNodes.size() + 2;

        writer.cell(id);
        writer.cell(modelPath);
        writer.cell(modelName);
        writer.cell(stateSpaceSize);
        writer.cell(finalMddSize);
        writer.cell(totalTime);
        writer.cell(ssgTime);
        writer.cell(nodeCount);
        writer.cell(unionCacheSize);
        writer.cell(unionQueryCount);
        writer.cell(unionHitCount);
        writer.cell(saturateCacheSize);
        writer.cell(saturateQueryCount);
        writer.cell(saturateHitCount);
        writer.cell(relProdCacheSize);
        writer.cell(relProdQueryCount);
        writer.cell(relProdHitCount);
        writer.cell(saturatedNodeCount);
        writer.newRow();
    }

    private void printSymbolicResult(
            TableWriter writer,
            MddVariableOrder variableOrder,
            PtNetSystem system,
            MddHandle result,
            BfsProvider provider,
            long totalTime,
            long ssgTime
    ) {
        String id = this.id;
        String modelPath = this.model;
        String modelName = system.getName();

        Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(result);
        long nodeCount = variableOrder.getMddGraph().getUniqueTableSize();

        long unionCacheSize = variableOrder.getDefaultUnionProvider().getCacheSize();
        long unionQueryCount = variableOrder.getDefaultUnionProvider().getQueryCount();
        long unionHitCount = variableOrder.getDefaultUnionProvider().getHitCount();

        long relProdCacheSize = provider.getRelProdCache().getCacheSize();
        long relProdQueryCount = provider.getRelProdCache().getQueryCount();
        long relProdHitCount = provider.getRelProdCache().getHitCount();

        final Set<MddNode> nodes = MddNodeCollector.collectNodes(result);
        long finalMddSize = nodes.size();

        writer.cell(id);
        writer.cell(modelPath);
        writer.cell(modelName);
        writer.cell(stateSpaceSize);
        writer.cell(finalMddSize);
        writer.cell(totalTime);
        writer.cell(ssgTime);
        writer.cell(nodeCount);
        writer.cell(unionCacheSize);
        writer.cell(unionQueryCount);
        writer.cell(unionHitCount);
        writer.cell(relProdCacheSize);
        writer.cell(relProdQueryCount);
        writer.cell(relProdHitCount);
        writer.newRow();
    }

    private void printError(final Throwable ex) {
        final String message = ex.getMessage() == null ? "" : ex.getMessage();
        if (benchmarkMode) {
            writer.cell("[EX] " + ex.getClass().getSimpleName() + ": " + message);
            writer.newRow();
        } else {
            logger.write(Logger.Level.RESULT, "%s occurred, message: %s%n", ex.getClass().getSimpleName(), message);
            if (stacktrace) {
                final StringWriter errors = new StringWriter();
                ex.printStackTrace(new PrintWriter(errors));
                logger.write(Logger.Level.RESULT, "Trace:%n%s%n", errors.toString());
            } else {
                logger.write(Logger.Level.RESULT, "Use --stacktrace for stack trace%n");
            }
        }
    }

    private void writeCex(final SafetyResult.Unsafe<?, ?> status, final XSTS xsts) throws FileNotFoundException {

        @SuppressWarnings("unchecked") final Trace<XstsState<?>, XstsAction> trace = (Trace<XstsState<?>, XstsAction>) status.getCex();
        final XstsStateSequence concrTrace = XstsTraceConcretizerUtil.concretize(trace, Z3LegacySolverFactory.getInstance(), xsts);
        final File file = new File(cexfile);
        try (PrintWriter printWriter = new PrintWriter(file)) {
            printWriter.write(concrTrace.toString());
        }
    }

    private void writeXstsMddVisualStatus(final SafetyResult<MddWitness, MddCex> status, final String filename)
            throws FileNotFoundException {
        final Graph graph = status.isSafe() ? new MddNodeVisualizer(XstsCli::nodeToString).visualize(status.asSafe().getWitness().getMdd().getNode())
                : new MddNodeVisualizer(XstsCli::nodeToString).visualize(status.asUnsafe().getCex().getMdd().getNode());
        GraphvizWriter.getInstance().writeFile(graph, filename);
    }

    private static String nodeToString(MddNode node) {
        if (node.getRepresentation() instanceof RecursiveIntObjMapViews.OfIntObjMapView<?, ?>)
            return "";
        return node instanceof MddNode.Terminal ? ((MddNode.Terminal<?>) node).getTerminalData().toString() : node.getRepresentation().toString();
    }

    private void writeVisualStatus(final SafetyResult<? extends ARG<?, ?>, ? extends Trace<? extends State, ? extends Action>> status, final String filename)
            throws FileNotFoundException {
        final Graph graph = status.isSafe() ? ArgVisualizer.getDefault().visualize(status.asSafe().getWitness())
                : TraceVisualizer.getDefault().visualize(status.asUnsafe().getCex());
        GraphvizWriter.getInstance().writeFile(graph, filename);
    }

    private static String reverseString(String str) {
        StringBuilder sb = new StringBuilder(str);
        sb.reverse();
        return sb.toString();
    }

    private static class MddNodeCollector {
        public static Set<MddNode> collectNodes(MddHandle root) {
            Set<MddNode> ret = HashObjSets.newUpdatableSet();
            collect(root.getNode(), ret);
            return ret;
        }

        private static void collect(MddNode node, Set<MddNode> result) {
            if (!result.add(node)) {
                return;
            }

            if (!node.isTerminal()) {
                for (IntObjCursor<? extends MddNode> c = node.cursor(); c.moveNext(); ) {
                    collect(c.value(), result);
                }
            }
        }
    }

    private void createDepGxl(PtNetSystem system) throws Exception {
        try {
            final File gxlFile = new File(depGxl);
            if (!gxlFile.exists()) {
                gxlFile.createNewFile();
            }
            final PrintStream gxlOutput = new PrintStream(gxlFile);

            // TODO: this would be better with the PetriNet file only.
            gxlOutput.print(PtNetDependency2Gxl.toGxl(system, false));
            gxlOutput.close();
        } catch (IOException e) {
            throw new Exception("Error creating GXL file: " + e.getMessage());
        }
    }

    private void createDepGxlGSat(PtNetSystem system) throws Exception {
        try {
            final File gxlFile = new File(depGxlGsat);
            if (!gxlFile.exists()) {
                gxlFile.createNewFile();
            }
            final PrintStream gxlOutput = new PrintStream(gxlFile);

            // TODO: this would be better with the PetriNet file only.
            gxlOutput.print(PtNetDependency2Gxl.toGxl(system, true));
            gxlOutput.close();
        } catch (IOException e) {
            throw new Exception("Error creating GXL file: " + e.getMessage());
        }
    }

    private void createDepMat(PtNetSystem system) throws Exception {
        try {
            final File depMatFile = new File(depMat);
            if (!depMatFile.exists()) {
                depMatFile.createNewFile();
            }
            final PrintStream depMatOutput = new PrintStream(depMatFile);

            // TODO: this would be better with the PetriNet file only.
            depMatOutput.print(system.printDependencyMatrixCsv());
            depMatOutput.close();
        } catch (IOException e) {
            throw new Exception("Error creating dependency matrix file: " + e.getMessage());
        }
    }

    private void createDepMatPng(PtNetSystem system) throws Exception {
        if (system.getPlaceCount() < 10000 && system.getTransitionCount() < 10000) {
            try {
                final BufferedImage image = system.dependencyMatrixImage(1);
                ImageIO.write(image, "PNG", new File(depMatPng));
            } catch (IOException e) {
                throw new Exception("Error creating dependency matrix file: " + e.getMessage());
            }
        } else {
            logger.write(Logger.Level.INFO, "[WARNING] Skipping image generation because the model size exceeds 10k places or " +
                    "transitions.");
        }
    }


    private void registerAllSolverManagers(String home, Logger logger) throws Exception {
        SolverManager.closeAll();
        SolverManager.registerSolverManager(Z3SolverManager.create());
        if (OsHelper.getOs() == OsHelper.OperatingSystem.LINUX) {
            SmtLibSolverManager smtLibSolverManager = SmtLibSolverManager.create(Path.of(home), logger);
            SolverManager.registerSolverManager(smtLibSolverManager);
        }
    }

}
