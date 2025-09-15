/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.smtlib.impl.generic;

import com.zaxxer.nuprocess.NuAbstractProcessHandler;
import com.zaxxer.nuprocess.NuProcessBuilder;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinary;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

/**
 * Instead of an interactive solver, these binaries can only work with an input file. Therefore, we
 * keep track of commands, and only execute them when readResponse() is called.
 */
public class GenericSmtLibOneshotSolverBinary implements SmtLibSolverBinary {

    private final List<String> commands;
    private final Path solverPath;
    private final String[] args;
    private final Map<String, String> env;

    public GenericSmtLibOneshotSolverBinary(
            Path solverPath, String[] args, Map<String, String> env) {
        this.solverPath = solverPath;
        this.args = args;
        this.env = env;
        commands = new ArrayList<>();
    }

    @Override
    public void issueCommand(String command) {
        commands.add(command);
    }

    @Override
    public String readResponse() {
        try {
            final File file = File.createTempFile("input", ".smt2");
            file.deleteOnExit();

            try (BufferedWriter bufferedWriter = new BufferedWriter(new FileWriter(file))) {
                for (String command : commands) {
                    bufferedWriter.write(command);
                    bufferedWriter.newLine();
                }
            }
            final var processCmd = new ArrayList<String>();
            processCmd.add(solverPath.toAbsolutePath().toString());
            processCmd.addAll(Arrays.asList(args));
            processCmd.add(file.getAbsolutePath());

            final var solverProcessBuilder = new NuProcessBuilder(processCmd);
            solverProcessBuilder.environment().putAll(env);
            final var handler = new ProcessHandler();
            solverProcessBuilder.setProcessListener(handler);

            final var proc = solverProcessBuilder.start();

            proc.waitFor(0, TimeUnit.SECONDS);

            return handler.getResponse();
        } catch (IOException | InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void close() throws Exception {
        // no-op
    }

    private static class ProcessHandler extends NuAbstractProcessHandler {
        private final StringBuilder response = new StringBuilder();

        @Override
        public void onStdout(ByteBuffer buffer, boolean closed) {
            if (!closed) {
                byte[] bytes = new byte[buffer.remaining()];
                buffer.get(bytes);
                final var str = new String(bytes);
                response.append(str);
            }
        }

        @Override
        public void onStderr(ByteBuffer buffer, boolean closed) {
            if (!closed) {
                byte[] bytes = new byte[buffer.remaining()];
                buffer.get(bytes);
                System.err.println(new String(bytes));
            }
        }

        public String getResponse() {
            return response.toString();
        }
    }
}
