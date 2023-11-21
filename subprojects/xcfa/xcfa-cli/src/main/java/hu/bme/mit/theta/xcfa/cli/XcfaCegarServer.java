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

package hu.bme.mit.theta.xcfa.cli;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Stopwatch;
import com.google.gson.Gson;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.debug.ARGWebDebugger;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.logging.ConsoleLabelledLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.xcfa.analysis.coi.XcfaCoiKt;
import hu.bme.mit.theta.xcfa.analysis.coi.XcfaCoiMultiThread;
import hu.bme.mit.theta.xcfa.analysis.coi.XcfaCoiSingleThread;
import hu.bme.mit.theta.xcfa.cli.utils.XcfaWitnessWriter;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;
import java.nio.file.FileSystems;
import java.util.concurrent.TimeUnit;
import java.util.zip.GZIPInputStream;

import static hu.bme.mit.theta.xcfa.cli.ExitCodesKt.exitOnError;
import static hu.bme.mit.theta.xcfa.cli.GsonUtilsKt.getGson;
import static hu.bme.mit.theta.xcfa.cli.SolverRegistrationKt.getSolver;

class XcfaCegarServer {
    @Parameter(names = "--port", description = "Port number for server to use")
    int port = 0;

    @Parameter(names = "--oneshot", description = "Exit after the first check()")
    boolean oneshot = true;

    @Parameter(names = "--smt-home", description = "The path of the solver registry")
    String solverHome = SmtLibSolverManager.HOME.toAbsolutePath().toString();

    @Parameter(names = "--return-safety-result", description = "If set, give back the safety result instead of writing witnesses directly.", arity = 1)
    boolean returnSafetyResult = false;

    @Parameter(names = "--input", description = "Original source file (required for witness writing)")
    String inputFileName;

    @Parameter(names = "--config", description = "Config string (will try to read from stdin when not given)")
    String configStr;

    @Parameter(names = "--xcfa", description = "XCFA string (will try to read from stdin when not given)")
    String xcfaStr;

    @Parameter(names = "--parse-context", description = "Parsing context string (will try to read from stdin when not given)")
    String parseContext;

    @Parameter(names = "--debug", description = "Debug mode (will not create a socket)")
    Boolean debug = false;


    @Parameter(names = "--arg-debug", description = "ARG debug mode (use the web-based debugger for ARG visualization)")
    Boolean argdebug = false;


    @Parameter(names = "--gzip", description = "Expect stdin to contain gzipped text")
    Boolean gzip = false;

    private void run(String[] args) {
        try {
            JCommander.newBuilder().addObject(this).build().parse(args);
        } catch (final ParameterException ex) {
            System.out.println("Invalid parameters, details:");
            System.out.println(ex.getMessage());
            ex.usage();
            System.exit(ExitCodes.INVALID_PARAM.getCode());
        }

        if (argdebug) ARGWebDebugger.on = true;

        final Logger logger = new ConsoleLabelledLogger();

        exitOnError(true, debug, () -> {
            SolverRegistrationKt.registerAllSolverManagers(solverHome, logger);
            try (final ServerSocket socket = new ServerSocket(port)) {
                logger.write(Logger.Level.INFO, "Server started on port " + socket.getLocalPort() + ".\n");
                System.out.println("Port=(" + socket.getLocalPort() + ")");
                do {
                    try (final Socket clientSocket = debug ? null : socket.accept()) {
                        final PrintWriter out = new PrintWriter(debug ? System.out : clientSocket.getOutputStream(), true);
                        InputStream stream = debug ? System.in : clientSocket.getInputStream();
                        if (gzip) {
                            stream = new GZIPInputStream(stream, 65536);
                            logger.write(Level.INFO, "Using GZIP compression\n");
                        }
                        final BufferedReader in = new BufferedReader(new InputStreamReader(stream));

                        final Stopwatch sw = Stopwatch.createStarted();

                        final String configStr = this.configStr == null ? in.readLine() : this.configStr;
                        logger.write(Level.INFO, "Read config in " + sw.elapsed(TimeUnit.MILLISECONDS) + "ms\n");
                        sw.reset().start();
                        final String xcfaStr = this.xcfaStr == null ? in.readLine() : this.xcfaStr;
                        logger.write(Level.INFO, "Read XCFA in " + sw.elapsed(TimeUnit.MILLISECONDS) + "ms\n");
                        sw.reset().start();
                        final String parseStr = this.parseContext == null ? in.readLine() : this.parseContext;
                        logger.write(Level.INFO, "Read ParseContext in " + sw.elapsed(TimeUnit.MILLISECONDS) + "ms\n");
                        sw.reset().start();
                        final Gson gson = getGson();

                        XCFA xcfa;
                        try {
                            xcfa = gson.fromJson(xcfaStr, XCFA.class);
                        } catch (Exception e) {
                            File tempFile = File.createTempFile("xcfa", ".json");
                            try (BufferedWriter bw = new BufferedWriter(new FileWriter(tempFile))) {
                                bw.write(xcfaStr);
                            }
                            System.err.println("Erroneous XCFA, see file " + tempFile.getAbsolutePath());
                            throw e;
                        }

                        logger.write(Logger.Level.INFO, "Parsed xcfa.\n");
                        XcfaCegarConfig xcfaCegarConfig;
                        try {
                            xcfaCegarConfig = gson.fromJson(configStr, XcfaCegarConfig.class);
                        } catch (Exception e) {
                            File tempFile = File.createTempFile("config", ".json");
                            try (BufferedWriter bw = new BufferedWriter(new FileWriter(tempFile))) {
                                bw.write(configStr);
                            }
                            System.err.println("Erroneous config, see file " + tempFile.getAbsolutePath());
                            throw e;
                        }

                        logger.write(Logger.Level.INFO, "Parsed config.\n");
                        ParseContext parseContext;
                        try {
                            parseContext = gson.fromJson(parseStr, ParseContext.class);
                        } catch (Exception e) {
                            File tempFile = File.createTempFile("parsecontext", ".json");
                            try (BufferedWriter bw = new BufferedWriter(new FileWriter(tempFile))) {
                                bw.write(parseStr);
                            }
                            System.err.println("Erroneous parsecontext, see file " + tempFile.getAbsolutePath());
                            throw e;
                        }
                        XcfaCoiKt.ConeOfInfluence =
                                (parseContext.getMultiThreading()) ?
                                        new XcfaCoiMultiThread(xcfa) :
                                        new XcfaCoiSingleThread(xcfa);

                        logger.write(Logger.Level.INFO, "Parsed parsecontext.\n");

                        logger.write(Level.INFO, "Parsed config, XCFA and ParseContext in " + sw.elapsed(TimeUnit.MILLISECONDS) + "ms\n");
                        sw.reset();

                        SafetyResult<ExprState, ExprAction> check = xcfaCegarConfig.check(xcfa, logger);
                        logger.write(Logger.Level.INFO, "Safety check done.\n");
                        if (returnSafetyResult) {
                            String s = gson.toJson(check);
                            out.println(s);
                        } else {
                            var workdir = FileSystems.getDefault().getPath("").toAbsolutePath();
                            var witnessfile = new File(workdir.toString() + File.separator + "witness.graphml");
                            new XcfaWitnessWriter().writeWitness(check, new File(inputFileName), getSolver(xcfaCegarConfig.getRefinementSolver(), xcfaCegarConfig.getValidateRefinementSolver()), parseContext, witnessfile);
                        }
                        logger.write(Logger.Level.INFO, "Server exiting.\n");
                    }
                } while (!oneshot);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
            return null;
        });
    }

    public static void main(String[] args) throws FileNotFoundException {
        new XcfaCegarServer().run(args);
    }
}
