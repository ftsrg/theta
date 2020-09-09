package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutablePartitionedValuation;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.*;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;

public class ExecutionGraph implements Runnable{
    private static final XcfaStmtExecutionVisitor xcfaStmtExecutionVisitor;

    private ThreadPoolExecutor threadPool;

    private static int cnt;
    private final int id;
    private final XCFA xcfa;                                                  //shallow
    private final Set<Write> initialWrites;                                   //shallow
    private final Map<XCFA.Process, MemoryAccess> lastNode;                   //deep
    private final Map<XCFA.Process, Map<VarDecl<?>, Read>> lastRead;          //deep
    private final Map<VarDecl<?>, List<Read>> revisitableReads;               //deep
    private final Map<VarDecl<?>, List<Write>> writes;                        //deep
    private final Map<Read, Tuple2<Write, Tuple2<MemoryAccess, String>>> fr;  //deep
    private final Map<MemoryAccess, Set<Tuple2<MemoryAccess, String>>> edges; //deep

    private final Map<XCFA.Process, List<StackFrame>> stackFrames;            //deep
    private final MutablePartitionedValuation mutablePartitionedValuation;    //deep
    private XCFA.Process currentlyAtomic;                                     //shallow

    private final Map<XCFA.Process, Integer> partitions;                      //shallow

    //CONSTRUCTORS

    private ExecutionGraph(XCFA xcfa) {
        initialWrites = new HashSet<>();
        lastNode = new HashMap<>();
        lastRead = new HashMap<>();
        revisitableReads = new HashMap<>();
        writes = new HashMap<>();
        fr = new HashMap<>();
        stackFrames = new HashMap<>();
        currentlyAtomic = null;
        mutablePartitionedValuation = new MutablePartitionedValuation();
        partitions = new HashMap<>();
        edges = new HashMap<>();
        this.xcfa = xcfa;

        xcfa.getProcesses().forEach(process -> {
            stackFrames.put(process, new ArrayList<>());
            partitions.put(process, mutablePartitionedValuation.createPartition());
            lastRead.put(process, new HashMap<>());
        });

        xcfa.getGlobalVars().forEach(varDecl -> {
            revisitableReads.put(varDecl, new ArrayList<>());
            writes.put(varDecl, new ArrayList<>());
            LitExpr<?> litExpr;
            if((litExpr = xcfa.getInitValue(varDecl)) != null) {
                addInititalWrite(varDecl, litExpr);
            }
        });
        id = cnt++;
    }

    private ExecutionGraph(
            ThreadPoolExecutor threadPool,
            XCFA xcfa,
            Set<Write> initialWrites,
            Map<XCFA.Process, MemoryAccess> lastNode,
            Map<XCFA.Process, Map<VarDecl<?>, Read>> lastRead,
            Map<VarDecl<?>, List<Read>> revisitableReads,
            Map<VarDecl<?>, List<Write>> writes,
            Map<MemoryAccess, Set<Tuple2<MemoryAccess, String>>> edges,
            Map<Read, Tuple2<Write, Tuple2<MemoryAccess, String>>> fr,
            Map<XCFA.Process, List<StackFrame>> stackFrames,
            XCFA.Process currentlyAtomic,
            MutablePartitionedValuation mutablePartitionedValuation,
            Map<XCFA.Process, Integer> partitions){
        this.threadPool = threadPool;
        this.xcfa = xcfa;
        this.initialWrites = initialWrites;
        this.lastNode = new HashMap<>(lastNode);
        this.fr = new HashMap<>(fr);
        this.lastRead = new HashMap<>();
        lastRead.forEach((process, varDeclReadMap) -> this.lastRead.put(process, new HashMap<>(varDeclReadMap)));
        this.revisitableReads = new HashMap<>();
        revisitableReads.forEach((varDecl, reads) -> this.revisitableReads.put(varDecl, new ArrayList<>(reads)));
        this.writes = new HashMap<>();
        writes.forEach((varDecl, writes1) -> this.writes.put(varDecl, new ArrayList<>(writes1)));
        this.edges = new HashMap<>();
        edges.forEach((memoryAccess, tuples) -> this.edges.put(memoryAccess, new HashSet<>(tuples)));
        this.stackFrames = new HashMap<>();
        stackFrames.forEach((process, stackFrames1) -> this.stackFrames.put(process, new ArrayList<>(stackFrames1)));
        this.stackFrames.forEach((process, stackFrameList) -> {
            int lastId = stackFrameList.size() - 1;
            if(lastId != -1) {
                StackFrame stackFrame;
                if (!(stackFrame = stackFrameList.get(lastId)).isLastStmt()) {
                    stackFrameList.remove(lastId);
                    stackFrameList.add(stackFrame.duplicate());
                }
            }
        });
        this.currentlyAtomic = currentlyAtomic;
        this.mutablePartitionedValuation = MutablePartitionedValuation.copyOf(mutablePartitionedValuation);
        this.partitions = partitions;
        id = cnt++;
    }

    // STATIC METHODS

    static {
        cnt = 0;
        xcfaStmtExecutionVisitor = new XcfaStmtExecutionVisitor();
    }

    /*
     * Create a new ExecutionGraph and return it
     */
    public static ExecutionGraph create(XCFA xcfa) {
        return new ExecutionGraph(xcfa);
    }





    // PUBLIC METHODS

    public void execute() {
        threadPool = new ThreadPoolExecutor(0, 1, 1, TimeUnit.SECONDS, new LinkedBlockingQueue<>());
        threadPool.execute(this);
        try {
            if(!threadPool.awaitTermination(600, TimeUnit.SECONDS)) {
                threadPool.shutdownNow();
            }
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    /*
     * Run the algorithm on the current ExecutionGraph
     */
    @Override
    public void run() {
        int step = 0;
        while(executeNextStmt())
        {
//            printGraph(step++);
            /*Intentionally left empty*/
        }
        printGraph(step);
        testQueue();
    }


    // PACKAGE-PRIVATE METHODS

    /*
     * Add a read node
     */
    void addRead(XCFA.Process proc, VarDecl<?> local, VarDecl<?> global) {
        Read read = new Read(
                global,
                local,
                mutablePartitionedValuation.getValuation(getPartitionId(proc)),
                stackFrames.get(proc),
                lastRead.get(proc).get(global),
                proc,
                currentlyAtomic == proc,
                lastNode.get(proc));
        lastRead.get(proc).put(global, read);
        addNode(proc, read);

        int size = writes.get(global).size();
        for(int i = 0; i < size; ++i) {
            Write write = writes.get(global).get(i);
            Tuple2<MemoryAccess, String> edge = Tuple2.of(read, "rf");
            if(i < size - 1) {
                ExecutionGraph executionGraph = duplicate();
                executionGraph.edges.get(write).add(edge);
                executionGraph.mutablePartitionedValuation.put(getPartitionId(proc),global,write.getValue());
                executionGraph.fr.put(read, Tuple2.of(write, edge));
                threadPool.execute(executionGraph);
//                System.out.println("Starting_" + executionGraph.id);
            }
            else {
                edges.get(write).add(Tuple2.of(read, "rf"));
                mutablePartitionedValuation.put(getPartitionId(proc),global,write.getValue());
                fr.put(read, Tuple2.of(write, edge));
                revisitableReads.get(global).add(read);
            }
        }

    }

    /*
     * Add a write node
     */
    void addWrite(XCFA.Process proc, VarDecl<?> local, VarDecl<?> global) {
        @SuppressWarnings("OptionalGetWithoutIsPresent") Write write = new Write(global, mutablePartitionedValuation.eval(local).get(), proc, lastNode.get(proc));
        addNode(proc, write);
        writes.get(global).add(write);

        List<List<Read>> revisitSets = getRevisitSets(global);
        for(int i = 0; i < revisitSets.size(); ++i) {
            List<Read> reads = revisitSets.get(i);
            if(i < revisitSets.size() - 1) {
                ExecutionGraph executionGraph = duplicate();
                for(Read read : reads) {
                    Tuple2<MemoryAccess, String> edge = Tuple2.of(read, "rf");
                    executionGraph.revisitRead(read);
                    executionGraph.edges.get(write).add(edge);
                    executionGraph.fr.put(read, Tuple2.of(write, edge));
                    executionGraph.mutablePartitionedValuation.put(getPartitionId(proc),global,write.getValue());

                }
                threadPool.execute(executionGraph);
//                System.out.println("Starting_" + executionGraph.id);
            }
            else {
                for(Read read : reads) {
                    Tuple2<MemoryAccess, String> edge = Tuple2.of(read, "rf");
                    revisitRead(read);
                    edges.get(write).add(edge);
                    fr.put(read, Tuple2.of(write, edge));
                    mutablePartitionedValuation.put(getPartitionId(proc),global,write.getValue());
                }
            }
        }

    }

    /*
     * Add an initial write node
     */
    void addInititalWrite(VarDecl<?> global, LitExpr<?> value) {
        Write write = new Write(global, value, null, null);
        edges.put(write, new HashSet<>());
        initialWrites.add(write);
        if(!writes.containsKey(global)) {
            writes.put(global, new ArrayList<>());
        }
        writes.get(global).add(write);
    }

    void setCurrentlyAtomic(XCFA.Process currentlyAtomic) {
        this.currentlyAtomic = currentlyAtomic;
    }


    int getPartitionId(XCFA.Process process) {
        return partitions.get(process);
    }





    //PRIVATE METHODS

    /*
     * Returns a duplicate of the current ExecutionGraph
     */
    private ExecutionGraph duplicate() {
        return new ExecutionGraph(threadPool, xcfa, initialWrites, lastNode, lastRead, revisitableReads, writes, edges, fr, stackFrames, currentlyAtomic, mutablePartitionedValuation, partitions);
    }

    /*
     * Returns the current revisit (sub)sets of variable 'global'
     */
    private List<List<Read>> getRevisitSets(VarDecl<?> global) {
        List<List<Read>> ret = new ArrayList<>();
        if(revisitableReads.get(global) == null) return ret;
        for(int i = 0; i < (1<<revisitableReads.get(global).size()); ++i) {
            List<Read> list = new ArrayList<>();
            for(int j = 0; j < revisitableReads.get(global).size(); ++j) {
                if((i & (1<<j)) != 0) {
                    list.add(revisitableReads.get(global).get(j));
                }
            }
            ret.add(list);
        }
        return ret.stream().filter(reads -> {
            Set<XCFA.Process> processes = new HashSet<>();
            for(Read r : reads) {
                processes.add(r.getParentProcess());
            }
            return processes.size() == reads.size();
        }).collect(Collectors.toList());
    }

    /*
     * Executes the next statement to execute
     */
    private boolean executeNextStmt() {
        for(XCFA.Process process : currentlyAtomic == null ? xcfa.getProcesses() : Collections.singleton(currentlyAtomic)) {
            StackFrame stackFrame;
            if(stackFrames.get(process).size() == 0) {
                if (handleNewEdge(process, process.getMainProcedure().getInitLoc())) {
                    return true;
                }
            }
            else if((stackFrame = stackFrames.get(process).get(stackFrames.get(process).size()-1)).isLastStmt()) {
                if (handleNewEdge(process, stackFrame.getEdge().getTarget())) {
                    return true;
                }
            }
            else {
                if (handleCurrentEdge(process, stackFrame)) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean handleNewEdge(XCFA.Process process, XCFA.Process.Procedure.Location newSource) {
        for(XCFA.Process.Procedure.Edge edge : newSource.getOutgoingEdges()) {
            boolean canExecute = true;
            for(Stmt stmt : edge.getStmts()) {
                if (stmt instanceof AssumeStmt) {
                    canExecute = ((BoolLitExpr) ((AssumeStmt) stmt).getCond().eval(mutablePartitionedValuation)).getValue();
                }
            }
            if(canExecute) {
                for(Stmt stmt : edge.getStmts()) {
                    List<StackFrame> stackFrameList = stackFrames.get(process);
                    StackFrame stackFrame;
                    if(stackFrameList.size() > 0 && (stackFrame = stackFrameList.get(stackFrameList.size() - 1)).isLastStmt()) {
                        stackFrameList.remove(stackFrame);
                    }
                    stackFrameList.add(new StackFrame(edge, stmt));
                    stmt.accept(xcfaStmtExecutionVisitor, Tuple3.of(mutablePartitionedValuation, process, this));
                    return true;
                }
            }
        }
        return false;
    }

    private boolean handleCurrentEdge(XCFA.Process process, StackFrame stackFrame) {
        Stmt nextStmt = null;
        boolean found = false;
        for (Stmt stmt : stackFrame.getEdge().getStmts()) {
            if (stmt == stackFrame.getStmt()){
                found = true;
            }
            else if(found) {
                nextStmt = stmt;
                break;
            }
        }
        if(nextStmt != null) {
            stackFrame.setStmt(nextStmt);
            nextStmt.accept(xcfaStmtExecutionVisitor, Tuple3.of(mutablePartitionedValuation, process, this));
            return true;
        }
        else {
            stackFrame.setLastStmt();
            return handleNewEdge(process, stackFrame.getEdge().getTarget());
        }
    }


    private void addNode(XCFA.Process proc, MemoryAccess memoryAccess) {
        edges.put(memoryAccess, new HashSet<>());
        if(lastNode.get(proc) != null) {
            edges.get(lastNode.get(proc)).add(Tuple2.of(memoryAccess, "po"));
        }
        else {
            initialWrites.forEach(write -> edges.get(write).add(Tuple2.of(memoryAccess, "po")));
        }
        lastNode.put(proc, memoryAccess);
    }


    private void revisitRead(Read read) {
        for(Read r : read.getPrecedingReads()) {
            revisitableReads.get(r.getGlobalVar()).remove(r);
        }
        invalidateFuture(read);
        lastNode.put(read.getParentProcess(), read);
    }

    private void invalidateFuture(Read read) {
        Map<XCFA.Process, Boolean> atomic = new HashMap<>();
        invalidateFuture(read, atomic);

        boolean foundOne = false;
        for (Map.Entry<XCFA.Process, Boolean> entry : atomic.entrySet()) {
            XCFA.Process process = entry.getKey();
            Boolean atomicity = entry.getValue();
            if (atomicity) {
                checkState(!foundOne, "Multiple processes cannot be concurrently atomic!");
                foundOne = true;
                currentlyAtomic = process;
            }
        }
    }

    private void invalidateFuture(MemoryAccess memoryAccess, Map<XCFA.Process, Boolean> atomic) {
        if(memoryAccess instanceof Read) {
            edges.get(fr.get(memoryAccess).get1()).remove(fr.get(memoryAccess).get2());
            fr.remove(memoryAccess);
            revisitableReads.get(memoryAccess.getGlobalVar()).remove(memoryAccess);
        }
        for(Tuple2<MemoryAccess, String> edge : edges.get(memoryAccess)) {
            invalidateFuture(edge.get1(), atomic);
        }
        atomic.put(memoryAccess.getParentProcess(), memoryAccess.revert(stackFrames, lastNode, mutablePartitionedValuation, getPartitionId(memoryAccess.getParentProcess())));
        edges.put(memoryAccess, new HashSet<>());
    }


    private synchronized void testQueue() {
        if(threadPool.getQueue().size() == 0) {
            threadPool.shutdown();
        }
    }

    /*
     * Prints the graph as a graphviz cluster
     */
    private void printGraph(int step) {
        System.out.println("subgraph cluster_" + id + "_" + step + " {");
        System.out.println("label=cluster_" + id + "_" + step);
        revisitableReads.forEach((varDecl, reads) -> reads.forEach(read -> System.out.println("\"" + read + "_" + id + "_" + step  + "\" [style=filled]")));
        edges.forEach((memoryAccess, tuples) -> tuples.forEach(tuple ->  System.out.println("\"" + memoryAccess + "_" + id + "_" + step  + "\"" + " -> " + "\"" + tuple.get1() + "_" + id + "_" + step  + "\"" + (tuple.get2().equals("po") ? "" : "[label=" + tuple.get2() + ",constraint=false,color=green,fontcolor=green,style=dashed]"))));
        System.out.println("}");
    }

}
