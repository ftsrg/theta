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
package hu.bme.mit.theta.xcfa.execgraph.cli;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.algorithm.mcm.analysis.CandidateExecutionGraph;
import hu.bme.mit.theta.analysis.algorithm.mcm.analysis.PartialSolver;
import hu.bme.mit.theta.cat.dsl.CatDslManager;
import hu.bme.mit.theta.common.CliUtils;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.graphsolver.compilers.pattern2expr.Pattern2ExprCompiler;
import hu.bme.mit.theta.graphsolver.patterns.constraints.GraphConstraint;
import hu.bme.mit.theta.graphsolver.solvers.SATGraphSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;

import java.io.File;
import java.nio.file.Path;
import java.util.Collection;
import java.util.concurrent.TimeUnit;

public class ExecutionGraphCli {
    private static final String JAR_NAME = "theta-exec-graph-cli.jar";
    private final String[] args;

    //////////// CONFIGURATION OPTIONS BEGIN ////////////

    //////////// input task ////////////

    @Parameter(names = "--graph", description = "Path of the partial graph (graphviz)", required = true)
    File graph;

    @Parameter(names = "--cat", description = "Path of the cat model", required = true)
    File cat;

    //////////// output data and statistics ////////////

    @Parameter(names = "--version", description = "Display version", help = true)
    boolean versionInfo = false;

    @Parameter(names = "--loglevel", description = "Detailedness of logging")
    Logger.Level logLevel = Logger.Level.MAINSTEP;

    //////////// SMTLib options ////////////

    @Parameter(names = "--smt-home", description = "The path of the solver registry")
    String home = SmtLibSolverManager.HOME.toAbsolutePath().toString();

    @Parameter(names = "--solver", description = "Sets the underlying SMT solver to use. Enter in format <solver_name>:<solver_version>, see theta-smtlib-cli.jar for more details. Enter \"Z3\" to use the legacy z3 solver.")
    String solver = "Z3";

    //////////// CONFIGURATION OPTIONS END ////////////

    public ExecutionGraphCli(final String[] args) {
        this.args = args;
    }

    public static void main(final String[] args) {
        final ExecutionGraphCli mainApp = new ExecutionGraphCli(args);
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

        Logger logger = new ConsoleLogger(logLevel);

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
        try (Solver solver = SolverManager.resolveSolverFactory(this.solver).createSolver()) {
            final Collection<GraphConstraint> mcm = CatDslManager.createMCM(cat);
            logger.write(Logger.Level.MAINSTEP, "CAT model parsed successfully\n");

            final CandidateExecutionGraph partialGraph = PartialGraphVisitor.getPartialGraph(this.graph);
            logger.write(Logger.Level.MAINSTEP, "Partial graph parsed successfully\n");

            var partialSolver = new PartialSolver<>(mcm, partialGraph, new Pattern2ExprCompiler(), new SATGraphSolver(solver));
            var solution = partialSolver.getSolution();
            logger.write(Logger.Level.MAINSTEP, "Solution ready:\n");
            if (solution != null) {
                logger.write(Logger.Level.RESULT, "Solution: " + solution + "\n");
            } else {
                logger.write(Logger.Level.RESULT, "No such solution exists.\n");
            }
        } catch (final Throwable t) {
            t.printStackTrace();
            System.exit(-1);
        }
        long elapsed = sw.elapsed(TimeUnit.MILLISECONDS);
        sw.stop();
        System.out.println("walltime: " + elapsed + " ms");
    }

    public static void registerAllSolverManagers(String home, Logger logger) throws Exception {
        SolverManager.closeAll();
        SolverManager.registerSolverManager(Z3SolverManager.create());
        if (OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
            final var homePath = Path.of(home);
            final var smtLibSolverManager = SmtLibSolverManager.create(homePath, logger);
            SolverManager.registerSolverManager(smtLibSolverManager);
        }
    }

}
