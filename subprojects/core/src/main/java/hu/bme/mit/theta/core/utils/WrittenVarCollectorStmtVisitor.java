package hu.bme.mit.theta.core.utils;

import java.util.Collection;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicBeginStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicEndStmt;
import hu.bme.mit.theta.core.stmt.xcfa.EnterWaitStmt;
import hu.bme.mit.theta.core.stmt.xcfa.ExitWaitStmt;
import hu.bme.mit.theta.core.stmt.xcfa.LoadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.MtxLockStmt;
import hu.bme.mit.theta.core.stmt.xcfa.MtxUnlockStmt;
import hu.bme.mit.theta.core.stmt.xcfa.NotifyAllStmt;
import hu.bme.mit.theta.core.stmt.xcfa.NotifyStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StoreStmt;
import hu.bme.mit.theta.core.stmt.xcfa.WaitStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaStmtVisitor;
import hu.bme.mit.theta.core.type.Type;

/** Collects all variables that are written to by a stmt.
 * Used for collecting data dependencies between stmts. */
final class WrittenVarCollectorStmtVisitor implements StmtVisitor<Collection<VarDecl<?>>, Void>, XcfaStmtVisitor<Collection<VarDecl<?>>, Void> {

    private static final class LazyHolder {
        private final static WrittenVarCollectorStmtVisitor INSTANCE = new WrittenVarCollectorStmtVisitor();
    }

    private WrittenVarCollectorStmtVisitor() {
    }

    static WrittenVarCollectorStmtVisitor getInstance() {
        return WrittenVarCollectorStmtVisitor.LazyHolder.INSTANCE;
    }

    @Override
    public Void visit(XcfaCallStmt stmt, Collection<VarDecl<?>> param) {
        // TODO the procedure's local variables are not added.
        // This is not a problem for xcfa-analysis, as they are not global vars.
        return null;
    }

    @Override
    public Void visit(StoreStmt storeStmt, Collection<VarDecl<?>> param) {
        param.add(storeStmt.getRhs());
        return null;
    }

    @Override
    public Void visit(LoadStmt loadStmt, Collection<VarDecl<?>> param) {
        param.add(loadStmt.getLhs());
        return null;
    }

    @Override
    public Void visit(AtomicBeginStmt atomicBeginStmt, Collection<VarDecl<?>> param) {
        // TODO collect all variables that are accessed from here?
        return null;
    }

    @Override
    public Void visit(AtomicEndStmt atomicEndStmt, Collection<VarDecl<?>> param) {
        return null;
    }

    @Override
    public Void visit(NotifyAllStmt notifyAllStmt, Collection<VarDecl<?>> param) {
        param.add(notifyAllStmt.getSyncVar());
        return null;
    }

    @Override
    public Void visit(NotifyStmt notifyStmt, Collection<VarDecl<?>> param) {
        param.add(notifyStmt.getSyncVar());
        return null;
    }

    @Override
    public Void visit(WaitStmt waitStmt, Collection<VarDecl<?>> param) {
        if (waitStmt.getMtxSyncVar().isPresent()) {
            param.add(waitStmt.getMtxSyncVar().get());
        }
        param.add(waitStmt.getCndSyncVar());
        return null;
    }

    @Override
    public Void visit(SkipStmt stmt, Collection<VarDecl<?>> param) {
        return null;
    }

    @Override
    public Void visit(AssumeStmt stmt, Collection<VarDecl<?>> param) {
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, Collection<VarDecl<?>> param) {
        param.add(stmt.getVarDecl());
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, Collection<VarDecl<?>> param) {
        param.add(stmt.getVarDecl());
        return null;
    }

    @Override
    public Void visit(XcfaStmt xcfaStmt, Collection<VarDecl<?>> param) {
        xcfaStmt.accept(this, param);
        return null;
    }

    @Override
    public Void visit(MtxLockStmt lockStmt, Collection<VarDecl<?>> param) {
        param.add(lockStmt.getSyncVar());
        return null;
    }

    @Override
    public Void visit(MtxUnlockStmt unlockStmt, Collection<VarDecl<?>> param) {
        // TODO is this needed here?
        param.add(unlockStmt.getSyncVar());
        return null;
    }

    @Override
    public Void visit(ExitWaitStmt exitWaitStmt, Collection<VarDecl<?>> param) {
        param.add(exitWaitStmt.getSyncVar());
        return null;
    }

    @Override
    public Void visit(EnterWaitStmt enterWaitStmt, Collection<VarDecl<?>> param) {
        param.add(enterWaitStmt.getSyncVar());
        return null;
    }
}
