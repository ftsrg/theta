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
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.stream.Collectors;

public class ExecutionGraph {

    private static final Queue<ExecutionGraph> executionGraphs;
    private static final XcfaStmtExecutionVisitor xcfaStmtExecutionVisitor;

    private final XCFA xcfa;                                                  //shallow
    private final Set<Write> initialWrites;                                   //shallow
    private final Map<XCFA.Process, MemoryAccess> lastNode;                   //deep
    private final Map<VarDecl<?>, List<Read>> revisitableReads;               //deep
    private final Map<VarDecl<?>, Set<Write>> writes;                         //deep
    private final Map<MemoryAccess, Tuple2<MemoryAccess, String>> edges;      //deep
    private final Map<Write, Read> fr;                                        //deep

    private final Map<XCFA.Process, List<StackFrame>> stackFrames;            //deep
    private final MutablePartitionedValuation mutablePartitionedValuation;    //deep
    private final Map<XCFA.Process, Integer> partitions;                      //shallow

    private XCFA.Process currentlyAtomic;                                     //shallow


    //CONSTRUCTORS

    private ExecutionGraph(XCFA xcfa) {
        initialWrites = new HashSet<>();
        lastNode = new HashMap<>();
        revisitableReads = new HashMap<>();
        writes = new HashMap<>();
        fr = new HashMap<>();
        stackFrames = new HashMap<>();
        currentlyAtomic = null;
        mutablePartitionedValuation = new MutablePartitionedValuation();
        partitions = new HashMap<>();
        edges = new HashMap<>();
        this.xcfa = xcfa;
        //TODO: initialize variables from xcfa
    }

    private ExecutionGraph(
            XCFA xcfa,
            Set<Write> initialWrites,
            Map<XCFA.Process, MemoryAccess> lastNode,
            Map<VarDecl<?>, List<Read>> revisitableReads,
            Map<VarDecl<?>, Set<Write>> writes,
            Map<MemoryAccess, Tuple2<MemoryAccess, String>> edges,
            Map<Write, Read> fr, Map<XCFA.Process,
            List<StackFrame>> stackFrames,
            XCFA.Process currentlyAtomic,
            MutablePartitionedValuation mutablePartitionedValuation,
            Map<XCFA.Process, Integer> partitions){
        this.xcfa = xcfa;
        this.initialWrites = initialWrites;
        this.lastNode = new HashMap<>(lastNode);
        this.revisitableReads = new HashMap<>(revisitableReads);
        this.writes = new HashMap<>(writes);
        this.edges = new HashMap<>(edges);
        this.fr = new HashMap<>(fr);
        this.stackFrames = new HashMap<>(stackFrames);
        this.stackFrames.forEach((process, stackFrameList) -> {
            int lastId = stackFrameList.size() - 1;
            StackFrame stackFrame;
            if(!(stackFrame = stackFrameList.get(lastId)).isLastStmt()) {
                stackFrameList.remove(lastId);
                stackFrameList.add(stackFrame.duplicate());
            }
        });
        this.currentlyAtomic = currentlyAtomic;
        this.mutablePartitionedValuation = MutablePartitionedValuation.copyOf(mutablePartitionedValuation);
        this.partitions = partitions;
    }

    // STATIC METHODS

    static {
        executionGraphs = new ConcurrentLinkedQueue<>();
        xcfaStmtExecutionVisitor = new XcfaStmtExecutionVisitor();
    }

    /*
     * Create a new ExecutionGraph and return a thread-safe queue containing
     * all current ExecutionGraphs waiting to be executed.
     */
    public static Queue<ExecutionGraph> create(XCFA xcfa) {
        executionGraphs.add(new ExecutionGraph(xcfa));
        return executionGraphs;
    }





    // PUBLIC METHODS

    /*
     * Run the algorithm on the current ExecutionGraph
     */
    public void execute() {
        while(executeNextStmt())
        {
            /*Intentionally left empty*/
        }
    }





    // PACKAGE-PRIVATE METHODS

    /*
     * Add a read node
     */
    void addRead(XCFA.Process proc, VarDecl<?> local, VarDecl<?> global) {
        //TODO: implement
    }

    /*
     * Add a write node
     */
    void addWrite(XCFA.Process proc, VarDecl<?> local, VarDecl<?> global) {
        //TODO: implement
    }

    /*
     * Add an initial write node
     */
    void addInititalWrite(VarDecl<?> global, LitExpr<?> value) {
        Write write = new Write(global, value, null);
        initialWrites.add(write);
        if(!writes.containsKey(global)) {
            writes.put(global, new HashSet<>());
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
        return new ExecutionGraph(xcfa, initialWrites, lastNode, revisitableReads, writes, edges, fr, stackFrames, currentlyAtomic, mutablePartitionedValuation, partitions);
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
            if((stackFrame = stackFrames.get(process).get(stackFrames.get(process).size()-1)).isLastStmt()) {
                if (handleNewEdge(process, stackFrame)) return true;
            }
            else {
                if (handleCurrentEdge(process, stackFrame)) return true;
            }
        }
        return false;
    }

    private boolean handleNewEdge(XCFA.Process process, StackFrame stackFrame) {
        XCFA.Process.Procedure.Location newSource = stackFrame.getEdge().getTarget();
        for(XCFA.Process.Procedure.Edge edge : newSource.getOutgoingEdges()) {
            for(Stmt stmt : edge.getStmts()) {
                boolean canExecute = true;
                if (stmt instanceof AssumeStmt) {
                    canExecute = ((BoolLitExpr) ((AssumeStmt) stmt).getCond().eval(mutablePartitionedValuation)).getValue();
                }
                if(canExecute) {
                    stmt.accept(xcfaStmtExecutionVisitor, Tuple3.of(mutablePartitionedValuation, process, this));
                    stackFrames.get(process).add(new StackFrame(edge, stmt));
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
            nextStmt.accept(xcfaStmtExecutionVisitor, Tuple3.of(mutablePartitionedValuation, process, this));
            stackFrame.setStmt(nextStmt);
            return true;
        }
        else {
            stackFrame.setLastStmt();
            return handleNewEdge(process, stackFrame);
        }
    }

    /*
     * Prints the graph as a graphviz cluster
     */
    private void printGraph() {}

}
