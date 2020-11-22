package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.common.Datalog;
import hu.bme.mit.theta.mcm.MCM;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XcfaState;
import hu.bme.mit.theta.xcfa.analysis.stateless.XcfaStatelessSettings;

import java.io.Writer;
import java.util.Optional;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

public class ExecutionGraph implements Runnable{
    // STATIC FIELDS AND METHODS
    private static XcfaStatelessSettings settings;
    private static XCFA xcfa;
    private static MCM mcm;
    private static ThreadPoolExecutor threadPool;
    private static ExecutionGraph violator;

    public static Optional<ExecutionGraph> execute(XCFA xcfa, MCM mcm, XcfaStatelessSettings settings) {
        ExecutionGraph.settings = settings;
        ExecutionGraph.xcfa = xcfa;
        ExecutionGraph.mcm = mcm;
        ExecutionGraph.threadPool= new ThreadPoolExecutor(settings.getThreadPoolSize(), settings.getThreadPoolSize(), 0, TimeUnit.SECONDS, new LinkedBlockingQueue<>());
        ExecutionGraph.violator = null;
        ExecutionGraph root = new ExecutionGraph(xcfa.initialState());
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

    // MEMBERS
    private final XcfaState currentState;
    private final Datalog edgeDb;
    private final Datalog.Relation labelledEdge;
    private final Datalog.Relation labelledNode;

    private ExecutionGraph(XcfaState initialState) {
        this.currentState = initialState;
        this.edgeDb = Datalog.createProgram();
        this.labelledEdge = this.edgeDb.createRelation(3);
        this.labelledNode = this.edgeDb.createRelation(2);

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
