package hu.bme.mit.theta.xcfa.analysis.statelessold.graph.node;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.analysis.statelessold.State;
import hu.bme.mit.theta.xcfa.analysis.statelessold.graph.Edge;

import java.util.HashSet;
import java.util.Set;

public abstract class Node {

    protected final XCFA.Process parentProcess;
    protected final Tuple2<XCFA.Process, XCFA.Process.Procedure.Edge> edgeBackup;
    protected final int firstStmtBackup;
    private final Set<Edge> incomingEdges;
    private final Set<Edge> outgoingEdges;

    public Node(XCFA.Process parentProcess, Tuple2<XCFA.Process, XCFA.Process.Procedure.Edge> edge, int firstStmt) {
        outgoingEdges = new HashSet<>();
        incomingEdges = new HashSet<>();
        this.parentProcess = parentProcess;
        this.edgeBackup = edge;
        this.firstStmtBackup = firstStmt;
    }

    public Set<Edge> getOutgoingEdges() {
    return outgoingEdges;
    }

    public Set<Edge> getIncomingEdges() {
        return incomingEdges;
    }

    public void addIncomingEdge(Edge edge) {
        incomingEdges.add(edge);
    }

    public void addOutgoingEdge(Edge edge) {
        outgoingEdges.add(edge);
    }

    public void invalidate(State state) {
        for(Edge e : outgoingEdges) {
            e.getTarget().invalidate(state);
            state.getExecutionGraph().removeNode(e.getTarget());
            if(e.getTarget() instanceof Read) {
                state.getCurrentLocs().put(e.getTarget().getParentProcess(), e.getTarget().edgeBackup.get2().getSource());
                state.getFirstStmt().put(e.getTarget().edgeBackup.get2(), e.getTarget().firstStmtBackup);
            }
            e.getTarget().getIncomingEdges().forEach(edge -> {
                edge.getSource().getOutgoingEdges().remove(edge);
            });
            e.getTarget().getIncomingEdges().clear();
        }
        outgoingEdges.clear();
    }

    public abstract Node duplicate();

    public XCFA.Process getParentProcess() {
        return parentProcess;
    }
}
