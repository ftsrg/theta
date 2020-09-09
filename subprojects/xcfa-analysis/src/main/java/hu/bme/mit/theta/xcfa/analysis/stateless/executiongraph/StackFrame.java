package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.XCFA;

class StackFrame {
    private final XCFA.Process.Procedure.Edge edge;
    private Stmt stmt;
    private boolean lastStmt;

    StackFrame(XCFA.Process.Procedure.Edge edge, Stmt stmt) {
        this.edge = edge;
        this.stmt = stmt;
        this.lastStmt = false;
    }

    XCFA.Process.Procedure.Edge getEdge() {
        return edge;
    }

    Stmt getStmt() {
        return stmt;
    }

    boolean isLastStmt() {
        return lastStmt;
    }

    void setLastStmt() {
        this.lastStmt = true;
    }

    void setStmt(Stmt stmt) {
        this.stmt = stmt;
    }

    StackFrame duplicate() {
        return new StackFrame(edge, stmt);
    }
}
