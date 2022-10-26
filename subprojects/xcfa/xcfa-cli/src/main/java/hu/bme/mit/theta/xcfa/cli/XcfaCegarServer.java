/*
 *  Copyright 2022 Budapest University of Technology and Economics
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
import com.google.gson.Gson;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.logging.ConsoleLabelledLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.io.*;
import java.net.ServerSocket;
import java.net.Socket;

import static hu.bme.mit.theta.xcfa.cli.GsonUtilsKt.getGson;

class XcfaCegarServer {
    @Parameter(names = "--port", description = "Port number for server to use")
    int port = 12345;

    @Parameter(names = "--oneshot", description = "Exit after the first check()")
    boolean oneshot = true;

    private void run(String[] args) {
        try {
            JCommander.newBuilder().addObject(this).build().parse(args);
        } catch (final ParameterException ex) {
            System.out.println("Invalid parameters, details:");
            System.out.println(ex.getMessage());
            ex.usage();
            System.exit(-1);
        }

        final Logger logger = new ConsoleLabelledLogger();
        logger.write(Logger.Level.INFO, "Server started on port " + port + ".\n");

        try(final ServerSocket socket = new ServerSocket(port)) {
            do {
                try(final Socket clientSocket = socket.accept()) {
                    final PrintWriter out = new PrintWriter(clientSocket.getOutputStream(), true);
                    final BufferedReader in = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));

                    final String configStr = in.readLine();
                    final String xcfaStr = in.readLine();
                    final Gson gson = getGson();

                    XCFA xcfa;
                    try{
                        xcfa = gson.fromJson(xcfaStr, XCFA.class);
                    } catch(Exception e) {
                        File tempFile = File.createTempFile("xcfa", ".json");
                        try(BufferedWriter bw = new BufferedWriter(new FileWriter(tempFile))) {
                            bw.write(xcfaStr);
                        }
                        System.err.println("Erroneous XCFA, see file " + tempFile.getAbsolutePath());
                        throw e;
                    }

                    logger.write(Logger.Level.INFO, "Parsed xcfa.\n");
                    XcfaCegarConfig xcfaCegarConfig;
                    try{
                        xcfaCegarConfig = gson.fromJson(configStr, XcfaCegarConfig.class);
                    } catch(Exception e) {
                        File tempFile = File.createTempFile("config", ".json");
                        try(BufferedWriter bw = new BufferedWriter(new FileWriter(tempFile))) {
                            bw.write(configStr);
                        }
                        System.err.println("Erroneous config, see file " + tempFile.getAbsolutePath());
                        throw e;
                    }

                    logger.write(Logger.Level.INFO, "Parsed config.\n");

                    SafetyResult<ExprState, ExprAction> check = xcfaCegarConfig.check(xcfa, logger);
                    logger.write(Logger.Level.INFO, "Safety check done.\n");
                    String s = gson.toJson(check);
                    out.println(s);
                    logger.write(Logger.Level.INFO, "Server exiting.\n");
                }
            } while(!oneshot);
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(-1);
        }
    }

    public static void main(String[] args) throws FileNotFoundException {
        new XcfaCegarServer().run(args);
    }
}