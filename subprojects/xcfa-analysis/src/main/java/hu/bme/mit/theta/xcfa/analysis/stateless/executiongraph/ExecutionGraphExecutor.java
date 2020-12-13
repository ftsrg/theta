package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.mcm.MCM;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XcfaState;
import hu.bme.mit.theta.xcfa.analysis.stateless.XcfaStatelessSettings;

import java.io.Writer;
import java.util.Optional;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

public class ExecutionGraphExecutor implements Runnable{
    private static XcfaStatelessSettings settings;
    private static XCFA xcfa;
    private static MCM mcm;
    private static ThreadPoolExecutor threadPool;
    private static ExecutionGraphExecutor violator;

    public static Optional<ExecutionGraphExecutor> execute(XCFA xcfa, MCM mcm, XcfaStatelessSettings settings) {
        ExecutionGraphExecutor.settings = settings;
        ExecutionGraphExecutor.xcfa = xcfa;
        ExecutionGraphExecutor.mcm = mcm;
        ExecutionGraphExecutor.threadPool= new ThreadPoolExecutor(settings.getThreadPoolSize(), settings.getThreadPoolSize(), 0, TimeUnit.SECONDS, new LinkedBlockingQueue<>());
        ExecutionGraphExecutor.violator = null;
        ExecutionGraphExecutor root = new ExecutionGraphExecutor(xcfa.initialState());
        root.start();
        try {
            if(!threadPool.awaitTermination(settings.getTimeS(), TimeUnit.SECONDS)) {
                threadPool.shutdownNow();
            }
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        return Optional.ofNullable(violator);
    }

    private final XcfaState currentState;
    private final ExecutionGraph executionGraph;

    private ExecutionGraphExecutor(XcfaState initialState) {
        this.currentState = initialState;
        this.executionGraph = new ExecutionGraph(initialState);
    }

    @Override
    public void run() {

    }

    public void printGraph(Writer writer) {

    }


    private void start() {
        if(!Thread.currentThread().isInterrupted()) {
            threadPool.execute(this);
        }
    }

}
