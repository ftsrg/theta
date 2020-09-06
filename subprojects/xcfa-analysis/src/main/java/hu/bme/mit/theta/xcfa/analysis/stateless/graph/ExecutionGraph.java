package hu.bme.mit.theta.xcfa.analysis.stateless.graph;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.core.decl.VarDecl;
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
    private final Map<XCFA.Process, List<Node>> processNodes;
    private final Set<Read> revisitableSet;
    private State state;

    public ExecutionGraph() {
        revisitableSet = new HashSet<>();
        initialWrites = new HashSet<>();
        processNodes = new HashMap<>();
    }

    public State executeXcfa(XCFA xcfa) {
        state = new State(xcfa);

        Tuple2<XCFA.Process, XCFA.Process.Procedure.Edge> edge;
        while( (edge = state.getOneStep()) != null) {

            if(edge.get2().getTarget().isErrorLoc()) {
                return state;
            }

            for (Stmt stmt : edge.get2().getStmts()) {
                stmt.accept(new XcfaStmtExecutionVisitor(), Tuple4.of(state.getMutableValuation(), state, edge.get1(), this));
            }

            state.getCurrentLocs().put(edge.get1(), edge.get2().getTarget());

        }

        return state;

    }

    public void addRead(VarDecl<?> local, VarDecl<?> global) {

    }

    public void addWrite(VarDecl<?> local, VarDecl<?> global) {

    }

    public void addInitialWrite(VarDecl<?> global, LitExpr<?> value) {

    }

}
