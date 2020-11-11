package hu.bme.mit.theta.xcfa;

import hu.bme.mit.theta.core.stmt.Stmt;

class XcfaStackFrame {
    private final XcfaState owner;
    private final XCFA.Process.Procedure.Edge edge;
    private Stmt stmt;
    private boolean lastStmt;

    XcfaStackFrame(XcfaState owner, XCFA.Process.Procedure.Edge edge, Stmt stmt) {
        this.owner = owner;
        this.edge = edge;
        this.stmt = stmt;
        this.lastStmt = false;
    }

    public XCFA.Process.Procedure.Edge getEdge() {
        return edge;
    }

    public Stmt getStmt() {
        return stmt;
    }

    public boolean isLastStmt() {
        return lastStmt;
    }

    void setLastStmt() {
        this.lastStmt = true;
    }

    void setStmt(Stmt stmt) {
        this.stmt = stmt;
    }

    XcfaStackFrame duplicate(XcfaState newOwner) {
        return new XcfaStackFrame(newOwner, edge, stmt);
    }

    public XCFA.Process getProcess() {
        return edge.getParent().getParent();
    }

    public XcfaState getOwner() {
        return owner;
    }

    public void accept() {
        owner.acceptOffer(this);
    }
}
