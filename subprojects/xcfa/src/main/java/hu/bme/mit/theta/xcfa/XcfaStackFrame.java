package hu.bme.mit.theta.xcfa;

import hu.bme.mit.theta.core.stmt.Stmt;

class XcfaStackFrame {
    private final XcfaState owner;
    private final XcfaProcedure.Edge edge;
    private Stmt stmt;
    private boolean lastStmt;
    private boolean newProcedure;

    XcfaStackFrame(XcfaState owner, XcfaProcedure.Edge edge, Stmt stmt) {
        this.owner = owner;
        this.edge = edge;
        this.stmt = stmt;
        this.lastStmt = false;
        this.newProcedure = false;
    }

    public XcfaProcedure.Edge getEdge() {
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

    public XcfaProcess getProcess() {
        return edge.getParent().getParent();
    }

    public XcfaState getOwner() {
        return owner;
    }

    public void accept() {
        owner.acceptOffer(this);
    }

    public boolean isNewProcedure() {
        return newProcedure;
    }

    public void setNewProcedure() {
        this.newProcedure = true;
    }
}
