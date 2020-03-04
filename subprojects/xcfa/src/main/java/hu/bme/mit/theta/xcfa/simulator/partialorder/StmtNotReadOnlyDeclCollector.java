package hu.bme.mit.theta.xcfa.simulator.partialorder;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.stmt.xcfa.*;
import hu.bme.mit.theta.core.type.Type;

import java.util.Collection;

/**
 * These declarations are used when a variable is not only read, but modified.
 * This is used to calculate whether two statements are independent.
 * The result must contain all elements that could change.
 * It is not a problem that it contains more elements (only the algorithm would be slower)
 */
public class StmtNotReadOnlyDeclCollector implements XcfaStmtVisitor<Collection<Decl<?>>, Void> {
    @Override
    public Void visit(XcfaCallStmt stmt, Collection<Decl<?>> param) {
        return null;
    }

    @Override
    public Void visit(StoreStmt storeStmt, Collection<Decl<?>> param) {
        // TODO finish later
        param.add(storeStmt.getLhs());
        param.add(storeStmt.getRhs());
        return null;
    }

    @Override
    public Void visit(LoadStmt loadStmt, Collection<Decl<?>> param) {
        // TODO finish later
        param.add(loadStmt.getLhs());
        param.add(loadStmt.getRhs());
        return null;
    }

    @Override
    public Void visit(AtomicBeginStmt atomicBeginStmt, Collection<Decl<?>> param) {
        // TODO atomic stmts will be harder: they depend on more complex things
        throw new UnsupportedOperationException();
    }

    @Override
    public Void visit(AtomicEndStmt atomicEndStmt, Collection<Decl<?>> param) {
        return null;
    }

    @Override
    public Void visit(NotifyAllStmt notifyAllStmt, Collection<Decl<?>> param) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Void visit(NotifyStmt notifyStmt, Collection<Decl<?>> param) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Void visit(WaitStmt waitStmt, Collection<Decl<?>> param) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Void visit(SkipStmt stmt, Collection<Decl<?>> param) {
        return null;
    }

    @Override
    public Void visit(AssumeStmt stmt, Collection<Decl<?>> param) {
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, Collection<Decl<?>> param) {
        param.add(stmt.getVarDecl());
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, Collection<Decl<?>> param) {
        param.add(stmt.getVarDecl());
        return null;
    }

    @Override
    public Void visit(XcfaStmt xcfaStmt, Collection<Decl<?>> param) {
        xcfaStmt.accept(this,param);
        return null;
    }

    private static class Holder {
        static StmtNotReadOnlyDeclCollector instance = new StmtNotReadOnlyDeclCollector();
    }
    public static StmtNotReadOnlyDeclCollector getInstance() {
        return StmtNotReadOnlyDeclCollector.Holder.instance;
    }
}
