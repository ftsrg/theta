/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.litmus.cli;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.graphsolver.patterns.constraints.GraphConstraint;
import hu.bme.mit.theta.cat.dsl.CatDslManager;
import hu.bme.mit.theta.common.CliUtils;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.frontend.litmus2xcfa.LitmusInterpreter;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.io.File;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static hu.bme.mit.theta.xcfa.model.VisualizerKt.toDot;

public class LitmusCli {
    private static final String JAR_NAME = "theta-litmus-cli.jar";
    private final String[] args;

    //////////// CONFIGURATION OPTIONS BEGIN ////////////

    //////////// input task ////////////

    @Parameter(names = "--litmus", description = "Path of the litmus test", required = true)
    File litmus;

    @Parameter(names = "--cat", description = "Path of the cat model", required = true)
    File cat;

    //////////// output data and statistics ////////////

    @Parameter(names = "--version", description = "Display version", help = true)
    boolean versionInfo = false;

    @Parameter(names = "--loglevel", description = "Detailedness of logging")
    Logger.Level logLevel = Logger.Level.MAINSTEP;

    @Parameter(names = "--visualize", description = "Visualize solutions")
    boolean visualize;
    @Parameter(names = "--print-xcfa", description = "Print xcfa as a DOT file")
    boolean printxcfa;

    //////////// SMTLib options ////////////

    @Parameter(names = "--smt-home", description = "The path of the solver registry")
    String home = SmtLibSolverManager.HOME.toAbsolutePath().toString();

    @Parameter(names = "--solver", description = "Sets the underlying SMT solver to use. Enter in format <solver_name>:<solver_version>, see theta-smtlib-cli.jar for more details. Enter \"Z3\" to use the legacy z3 solver.")
    String solver = "Z3";

    //////////// CONFIGURATION OPTIONS END ////////////

    private Logger logger;

    public LitmusCli(final String[] args) {
        this.args = args;
    }

    public static void main(final String[] args) {
        final LitmusCli mainApp = new LitmusCli(args);
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

        logger = new ConsoleLogger(logLevel);

        /// version
        if (versionInfo) {
            CliUtils.printVersion(System.out);
            return;
        }

        try {
            registerAllSolverManagers(home, logger);
        } catch (Exception e) {
            e.printStackTrace();
            return;
        }


        final Stopwatch sw = Stopwatch.createStarted();
        try {
            try (Solver solver = SolverManager.resolveSolverFactory(this.solver).createSolver()) {

                final Collection<GraphConstraint> mcm = CatDslManager.createMCM(cat);
                logger.write(Logger.Level.MAINSTEP, "CAT model parsed successfully\n");
                final XCFA xcfa = LitmusInterpreter.getXcfa(litmus);
                logger.write(Logger.Level.MAINSTEP, "Litmus test parsed successfully\n");

                if (printxcfa) {
                    System.out.println("digraph G{");
                    //TODO visualize
                    System.out.println("}");
                }

//            final List<Integer> processIds = listToRange(processes, -1, -1);
//
//            final XcfaProcessMemEventProvider<ExplState> memEventProvider = new XcfaProcessMemEventProvider<>(processes.size());
//            final MultiprocLTS<XcfaProcessState<ExplState>, XcfaProcessAction> multiprocLTS = new MultiprocLTS<>(processIds.stream().map(id -> Map.entry(id, new XcfaProcessLTS<ExplState>())).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
//            final MultiprocInitFunc<XcfaProcessState<ExplState>, ExplPrec> multiprocInitFunc = new MultiprocInitFunc<>(processIds.stream().map(id -> Map.entry(id, new XcfaProcessInitFunc<>(processes.get(id * -1 - 1), ExplInitFunc.create(solver, True())))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
//            final MultiprocTransFunc<XcfaProcessState<ExplState>, XcfaProcessAction, ExplPrec> multiprocTransFunc = new MultiprocTransFunc<>(processIds.stream().map(id -> Map.entry(id, new XcfaProcessTransFunc<>(ExplStmtTransFunc.create(solver, 10)))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
//            final List<MemoryEvent.Write> initialWrites = xcfa.getvars().stream().filter(it -> xcfa.getInitValue(it).isPresent()).map(it -> new MemoryEvent.Write(memEventProvider.getVarId(it), it, null, Set.of(), null)).collect(Collectors.toList());
//            final XcfaProcessPartialOrd<ExplState> partialOrd = new XcfaProcessPartialOrd<>(ExplOrd.getInstance());


//			final XcfaProcessMemEventProvider<ExplState> memEventProvider = new XcfaProcessMemEventProvider<>(processes.size());
//			final MultiprocLTS<XcfaProcessState<ExplState>, XcfaProcessAction> multiprocLTS = new MultiprocLTS<>(processIds.stream().map(id -> Map.entry(id, new XcfaProcessLTS<ExplState>())).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
//			final MultiprocInitFunc<XcfaProcessState<ExplState>, ExplPrec> multiprocInitFunc = new MultiprocInitFunc<>(processIds.stream().map(id -> Map.entry(id, new XcfaProcessInitFunc<>(processes.get(id*-1-1), ExplInitFunc.create(solver, True())))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
//			final MultiprocTransFunc<XcfaProcessState<ExplState>, XcfaProcessAction, ExplPrec> multiprocTransFunc = new MultiprocTransFunc<>(processIds.stream().map(id -> Map.entry(id, new XcfaProcessTransFunc<>(ExplStmtTransFunc.create(solver, 10)))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
//			final List<MemoryEvent.Write> initialWrites = xcfa.getvars().stream().filter(it -> xcfa.getInitValue(it).isPresent()).map(it -> new MemoryEvent.Write(memEventProvider.getVarId(it), it, null, Set.of(), null)).collect(Collectors.toList());
//			final XcfaProcessPartialOrd<ExplState> partialOrd = new XcfaProcessPartialOrd<>(ExplOrd.getInstance());
//
//            final MutableValuation val = new MutableValuation();
//            for (VarDecl<? extends Type> var : xcfa.getvars()) {
//                val.put(var, BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, 64));
//            }
//
//            final MCMChecker<XcfaProcessState<ExplState>, XcfaProcessAction, ExplPrec> mcmChecker = new MCMChecker<>(memEventProvider, multiprocLTS, multiprocInitFunc, multiprocTransFunc, processIds, initialWrites, partialOrd, ExplState.of(val), solver, mcm, logger);
//            final MCMChecker.MCMSafetyResult mcmSafetyResult = mcmChecker.check(ExplPrec.of(xcfa.getvars().stream().filter(e -> e.getName().equals("crit")).toList()));
//            if (visualize) {
//                if (mcmSafetyResult.getSolutions().size() == 0) {
//                    logger.write(Logger.Level.RESULT, "No solutions found, nothing to visualize\n");
//                } else {
//                    mcmSafetyResult.visualize();
//                }
//            }
            }
        } catch (final Throwable t) {
            t.printStackTrace();
            System.exit(-1);
        }
        long elapsed = sw.elapsed(TimeUnit.MILLISECONDS);
        sw.stop();
        System.out.println("walltime: " + elapsed + " ms");
    }

    private <T> List<Integer> listToRange(List<T> list, int start, int d) {
        final List<Integer> elements = new ArrayList<>();
        for (int i = 0; i < list.size(); i++) {
            elements.add(i * d + start);
        }
        return elements;
    }

    public static void registerAllSolverManagers(String home, Logger logger) throws Exception {
//        CpuTimeKeeper.saveSolverTimes();
        SolverManager.closeAll();
        // register solver managers
        SolverManager.registerSolverManager(Z3SolverManager.create());
        if (OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
            final var homePath = Path.of(home);
            final var smtLibSolverManager = SmtLibSolverManager.create(homePath, logger);
            SolverManager.registerSolverManager(smtLibSolverManager);
        }
    }

}
