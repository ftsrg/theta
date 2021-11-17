package hu.bme.mit.theta.solver.smtlib.impl.generic;

import com.zaxxer.nuprocess.NuAbstractProcessHandler;
import com.zaxxer.nuprocess.NuProcess;
import com.zaxxer.nuprocess.NuProcessBuilder;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinaryException;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinary;

import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.Queue;

import static com.google.common.base.Preconditions.checkState;

public final class GenericSmtLibSolverBinary implements SmtLibSolverBinary {

    private final NuProcess solverProcess;
    private final ProcessHandler processHandler;

    public GenericSmtLibSolverBinary(final Path solverPath, final String[] args) {
        this(solverPath, args, false);
    }

    public GenericSmtLibSolverBinary(final Path solverPath, final String[] args, final boolean isCvc4) {
        final var processCmd = new ArrayList<String>();
        processCmd.add(solverPath.toAbsolutePath().toString());
        processCmd.addAll(Arrays.asList(args));

        final var solverProcessBuilder = new NuProcessBuilder(processCmd);

        processHandler = new ProcessHandler(isCvc4);
        solverProcessBuilder.setProcessListener(processHandler);

        solverProcess = solverProcessBuilder.start();
        checkState(solverProcess.isRunning());
    }

    @Override
    public void issueCommand(final String command) {
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

    private static final class ProcessHandler extends NuAbstractProcessHandler {
        private final Queue<String> inputQueue = new LinkedList<>();

        private final Queue<String> outputQueue = new LinkedList<>();
        private ReadProcessor readProcessor = null;
        private final boolean isCvc4;

        public ProcessHandler(final boolean isCvc4) {
            this.isCvc4 = isCvc4;
        }

        public synchronized void write(final String input) {
            inputQueue.add(input);
        }

        public synchronized String read() throws InterruptedException {
            while(outputQueue.isEmpty()) {
                wait();
            }

            return outputQueue.remove();
        }

        @Override
        public synchronized boolean onStdinReady(final ByteBuffer buffer) {
            while(!inputQueue.isEmpty()) {
                buffer.put(inputQueue.remove().getBytes(StandardCharsets.US_ASCII));
                buffer.put("\n".getBytes(StandardCharsets.US_ASCII));
            }
            buffer.flip();
            return false;
        }

        @Override
        public synchronized void onStdout(final ByteBuffer buffer, final boolean closed) {
            onInput(buffer);
        }

        @Override
        public synchronized void onStderr(final ByteBuffer buffer, final boolean closed) {
            onInput(buffer);
        }
        private int isFp = 0;
        private synchronized void onInput(final ByteBuffer buffer) {
            final var buf = new byte[buffer.remaining()];
            buffer.get(buf);
            final var input = new String(buf, StandardCharsets.US_ASCII);


            for(var c : input.toCharArray()) {
                if(readProcessor == null) {
                    readProcessor = new ReadProcessor();
                }

                readProcessor.step(c);
                if(isCvc4) {
                    if (c == 'f') {
                        isFp = 1;
                    } else if (isFp == 1 && c == 'p') {
                        isFp = 2;
                    } else if (isFp == 2 && c == ' ') {
                        isFp = 3;
                    } else if (isFp == 3 && c == ')') {
                        isFp = 0;
                        readProcessor.step(c);
                    } else if (isFp < 3){
                        isFp = 0;
                    }
                }


                if(readProcessor.isReady()) {
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
            INIT, LINE, PARENTHESES, STRING, COMMENT, READY
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
