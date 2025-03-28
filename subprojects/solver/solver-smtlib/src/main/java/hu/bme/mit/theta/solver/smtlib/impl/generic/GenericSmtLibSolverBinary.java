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

import static com.google.common.base.Preconditions.checkState;
import static java.lang.Math.min;

import com.zaxxer.nuprocess.NuAbstractProcessHandler;
import com.zaxxer.nuprocess.NuProcess;
import com.zaxxer.nuprocess.NuProcessBuilder;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinaryException;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.*;

public final class GenericSmtLibSolverBinary implements SmtLibSolverBinary {

    private final NuProcess solverProcess;
    private final ProcessHandler processHandler;
    private final List<String> issuedCommands = new ArrayList<>();

    public GenericSmtLibSolverBinary(final Path solverPath, final String[] args) {
        this(solverPath, args, EnumSet.noneOf(Solver.class));
    }

    public GenericSmtLibSolverBinary(
            final Path solverPath, final String[] args, final EnumSet<Solver> solverOverride) {
        final var processCmd = new ArrayList<String>();
        processCmd.add(solverPath.toAbsolutePath().toString());
        processCmd.addAll(Arrays.asList(args));

        final var solverProcessBuilder = new NuProcessBuilder(processCmd);

        processHandler = new ProcessHandler(solverOverride);
        solverProcessBuilder.setProcessListener(processHandler);

        solverProcess = solverProcessBuilder.start();
        try {
            Thread.sleep(50);
        } catch (InterruptedException ignored) {

        }
        checkState(solverProcess.isRunning());
    }

    @Override
    public void issueCommand(final String command) {
        issuedCommands.add(command);
        checkState(solverProcess.isRunning());
        processHandler.write(command);
        solverProcess.wantWrite();
    }

    @Override
    public String readResponse() {
        checkState(solverProcess.isRunning());
        try {
            return processHandler.read().trim();
        } catch (InterruptedException e) {
            throw new SmtLibSolverBinaryException(e);
        }
    }

    @Override
    public void close() {
        solverProcess.destroy(true);
    }

    public enum Solver {
        CVC4,
        PRINCESS
    }

    private static final class ProcessHandler extends NuAbstractProcessHandler {

        private final Queue<String> inputQueue = new LinkedList<>();
        private int headDoneIndex = 0;

        private final Queue<String> outputQueue = new LinkedList<>();
        private ReadProcessor readProcessor = null;
        private final boolean isCvc4;
        private final boolean isPrincess;

        public ProcessHandler(final EnumSet<Solver> solverOverride) {
            this.isCvc4 = solverOverride.contains(Solver.CVC4);
            this.isPrincess = solverOverride.contains(Solver.PRINCESS);
        }

        public synchronized void write(final String input) {
            inputQueue.add(input);
        }

        public synchronized String read() throws InterruptedException {
            while (outputQueue.isEmpty()) {
                wait();
            }

            return outputQueue.remove();
        }

        @Override
        public synchronized boolean onStdinReady(final ByteBuffer buffer) {
            if (!inputQueue.isEmpty()) {
                final var output = inputQueue.peek();
                final var eol = "\n".getBytes(StandardCharsets.US_ASCII);
                final var cutoff =
                        min(buffer.remaining() - eol.length, output.length() - headDoneIndex);
                buffer.put(
                        output.substring(headDoneIndex, headDoneIndex + cutoff)
                                .getBytes(StandardCharsets.US_ASCII));
                if (headDoneIndex + cutoff < output.length()) {
                    headDoneIndex = headDoneIndex + cutoff;
                } else {
                    inputQueue.remove();
                    headDoneIndex = 0;
                    buffer.put(eol);
                }
            }
            buffer.flip();
            return !inputQueue.isEmpty();
        }

        @Override
        public synchronized void onStdout(final ByteBuffer buffer, final boolean closed) {
            onInput(buffer);
        }

        @Override
        public synchronized void onStderr(final ByteBuffer buffer, final boolean closed) {
            if (!isPrincess) {
                onInput(buffer);
            }
        }

        private int isFp = 0;

        private synchronized void onInput(final ByteBuffer buffer) {
            final var buf = new byte[buffer.remaining()];
            buffer.get(buf);
            final var input = new String(buf, StandardCharsets.US_ASCII);
            // System.out.println(input);

            for (var c : input.toCharArray()) {
                if (readProcessor == null) {
                    readProcessor = new ReadProcessor();
                }

                readProcessor.step(c);
                if (isCvc4) {
                    if (c == 'f') {
                        isFp = 1;
                    } else if (isFp == 1 && c == 'p') {
                        isFp = 2;
                    } else if (isFp == 2 && c == ' ') {
                        isFp = 3;
                    } else if (isFp == 3 && c == ')') {
                        isFp = 0;
                        readProcessor.step(c);
                    } else if (isFp < 3) {
                        isFp = 0;
                    }
                }

                if (readProcessor.isReady()) {
                    isFp = 0;
                    outputQueue.add(readProcessor.getResult());
                    notifyAll();
                    readProcessor = null;
                }
            }
        }
    }

    private static final class ReadProcessor {

        private enum ReadStatus {
            INIT,
            LINE,
            PARENTHESES,
            STRING,
            COMMENT,
            READY
        }

        private ReadProcessor.ReadStatus status = ReadProcessor.ReadStatus.INIT;
        private int level = 0;

        private final StringBuilder sb = new StringBuilder(1024);

        public void step(final char c) {
            switch (status) {
                case INIT:
                    if (c == '(') {
                        level++;
                        sb.append(c);
                        status = ReadProcessor.ReadStatus.PARENTHESES;
                    } else if (c == ';') {
                        status = ReadProcessor.ReadStatus.COMMENT;
                    } else if (Character.isAlphabetic(c)) {
                        sb.append(c);
                        status = ReadProcessor.ReadStatus.LINE;
                    }
                    break;
                case LINE:
                    if (c == '\n') {
                        status = ReadProcessor.ReadStatus.READY;
                    } else {
                        sb.append(c);
                    }
                    break;
                case PARENTHESES:
                    sb.append(c);
                    if (c == '(') {
                        level++;
                    } else if (c == ')') {
                        level--;
                        if (level == 0) {
                            status = ReadProcessor.ReadStatus.READY;
                        }
                    } else if (c == '"') {
                        status = ReadProcessor.ReadStatus.STRING;
                    }
                    break;
                case STRING:
                    sb.append(c);
                    if (c == '"') {
                        status = ReadProcessor.ReadStatus.PARENTHESES;
                    }
                    break;
                case COMMENT:
                    if (c == '\n') {
                        status = ReadProcessor.ReadStatus.INIT;
                    }
                    break;
                case READY:
                default:
                    throw new AssertionError();
            }
        }

        public String getResult() {
            return sb.toString();
        }

        public boolean isReady() {
            return status == ReadProcessor.ReadStatus.READY;
        }
    }
}
