package hu.bme.mit.theta.xcfa.analysis.stateless.graph;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.analysis.stateless.State;
import hu.bme.mit.theta.xcfa.analysis.stateless.XcfaStmtExecutionVisitor;
import hu.bme.mit.theta.xcfa.analysis.stateless.graph.node.Node;
import hu.bme.mit.theta.xcfa.analysis.stateless.graph.node.Read;
import hu.bme.mit.theta.xcfa.analysis.stateless.graph.node.Write;

import java.util.*;

public class ExecutionGraph {
    private final Set<Write> initialWrites;
    private final Map<VarDecl<?>, List<Read>> revisitableReads;
    private final Map<VarDecl<?>, List<Write>> revisitableWrites;
    private final Map<XCFA.Process, List<Node>> nodes;
    private final State currentState;


    public ExecutionGraph(XCFA xcfa) {
        this.currentState = new State(xcfa);
        this.revisitableReads = new HashMap<>();
        nodes = new HashMap<>();
        initialWrites = new HashSet<>();
        revisitableWrites = new HashMap<>();

        for(VarDecl<?> varDecl : xcfa.getGlobalVars()) {
            if(varDecl.getInitValue() != null) {
                addInitialWrite(varDecl, varDecl.getInitValue());
            }
        }
    }

    private ExecutionGraph(
            Set<Write> initialWrites,
            Map<VarDecl<?>, List<Read>> revisitableReads,
            Map<VarDecl<?>, List<Write>> revisitableWrites,
            Map<XCFA.Process, List<Node>> nodes,
            State currentState) {
        this.initialWrites = new HashSet<>(initialWrites);
        this.revisitableReads = new HashMap<>();
        revisitableReads.forEach((varDecl, reads) -> this.revisitableReads.put(varDecl, new ArrayList<>(reads)));
        this.revisitableWrites = new HashMap<>();
        revisitableWrites.forEach((varDecl, writes) -> this.revisitableWrites.put(varDecl, new ArrayList<>(writes)));
        this.nodes = new HashMap<>();
        nodes.forEach((process, nodes1) -> this.nodes.put(process, new ArrayList<>(nodes1))); // TODO: deep copy nodes and edges
        this.currentState = State.copyOf(currentState);
    }

    public static ExecutionGraph copyOf(ExecutionGraph executionGraph) {
        return new ExecutionGraph(
                executionGraph.initialWrites,
                executionGraph.revisitableReads,
                executionGraph.revisitableWrites,
                executionGraph.nodes,
                executionGraph.currentState);
    }

    public void execute() {
        Tuple2<XCFA.Process, XCFA.Process.Procedure.Edge> edge;
        while((edge = currentState.getOneStep()) != null) {

            currentState.getCurrentLocs().put(edge.get1(), edge.get2().getTarget());

            if(edge.get2().getTarget().isErrorLoc()) {
                System.out.println("Error location reachable!");
            }


            for(Stmt stmt : edge.get2().getStmts()) {
                stmt.accept(new XcfaStmtExecutionVisitor(), Tuple4.of(currentState.getMutablePartitionedValuation(), currentState, edge.get1(), this));
            }

         }
        System.out.println("Execution graph finished!");

    }

    private void addNode(XCFA.Process proc, Node node) {
        if(nodes.containsKey(proc)) {
            Node last = nodes.get(proc).get(nodes.get(proc).size()-1);
            Edge edge = new Edge(last, node, "po");
            last.addOutgoingEdge(edge);
            node.addIncomingEdge(edge);
        }
        else {
            nodes.put(proc, new ArrayList<>());
            for(Write w : initialWrites) {
                Edge edge = new Edge(w, node, "po");
                w.addOutgoingEdge(edge);
                node.addIncomingEdge(edge);
            }
        }
    }

    public void addRead(XCFA.Process proc, VarDecl<?> local, VarDecl<?> global) {
        Read read;
        if(nodes.containsKey(proc)) {
            read = new Read(currentState.getMutablePartitionedValuation().getValuation(currentState.getPartitionId(proc)), global, local, proc);
        }
        else {
            read = new Read(new MutableValuation(), global, local, proc);
        }
        addNode(proc, read);

        List<Write> writes = revisitableWrites.get(global);
        if(writes == null) {
            throw new UnsupportedOperationException("Reading before writing is not yet supported");
        }

        for(int i = 0; i < writes.size(); ++i) {
            Write write = writes.get(i);
            ExecutionGraph executionGraph;
            if(i == writes.size()-1) {
                executionGraph = this;
                if(!revisitableReads.containsKey(global)) {
                    revisitableReads.put(global, new ArrayList<>());
                }
                revisitableReads.get(global).add(read);
                executionGraph.currentState.getMutablePartitionedValuation().put(executionGraph.currentState.getPartitionId(proc), local, write.getValue());
                // TODO: add rf edges
            }
            else {
                executionGraph = ExecutionGraph.copyOf(this);
                executionGraph.currentState.getMutablePartitionedValuation().put(executionGraph.currentState.getPartitionId(proc), local, write.getValue());
                executionGraph.execute();
            }
        }

    }

    public void addWrite(XCFA.Process proc, VarDecl<?> local, VarDecl<?> global) {
        Write write = new Write(global, currentState.getMutablePartitionedValuation().eval(local).get());
        addNode(proc, write);
        if(!revisitableWrites.containsKey(global)) {
            revisitableWrites.put(global, new ArrayList<>());
        }
        revisitableWrites.get(global).add(write);
        boolean firstDone = false;
        for(List<Read> reads : getRevisitSets(global)) {
            ExecutionGraph executionGraph;
            if(firstDone) {
                executionGraph = ExecutionGraph.copyOf(this);
            }
            else {
                executionGraph = this;
                firstDone = true;
            }
            for(Read read : reads) {
                read.invalidate(executionGraph.currentState);
                executionGraph.currentState.getMutablePartitionedValuation().put(executionGraph.currentState.getPartitionId(read.getParentProcess()), read.getLocal(), write.getValue());
            }
            // TODO: add rf edges
        }
    }

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
        return ret;
    }

    public void addInitialWrite(VarDecl<?> global, LitExpr<?> value) {
        Write write = new Write(global, value);
        initialWrites.add(write);
        if(!revisitableWrites.containsKey(global)) {
            revisitableWrites.put(global, new ArrayList<>());
        }
        revisitableWrites.get(global).add(write);
    }

}
