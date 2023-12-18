package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.clocktype.ClockType;

import java.util.Collection;

import static hu.bme.mit.theta.core.stmt.Stmts.Assume;

// handles delay stmts correctly
public class StmtContainsTimingVisitor implements StmtVisitor<Void, Boolean>  {

    private static final class LazyHolder {
        private final static StmtContainsTimingVisitor INSTANCE = new StmtContainsTimingVisitor();
    }

    private StmtContainsTimingVisitor() {
    }

    public static StmtContainsTimingVisitor getInstance() {
        return StmtContainsTimingVisitor.LazyHolder.INSTANCE;
    }

    @Override
    public Boolean visit(SkipStmt stmt, Void param) {
        return false;
    }

    @Override
    public Boolean visit(AssumeStmt stmt, Void param) {
        return containsClockVar(stmt);
    }

    @Override
    public <DeclType extends Type> Boolean visit(AssignStmt<DeclType> stmt, Void param) {
        return containsClockVar(stmt);
    }

    @Override
    public <DeclType extends Type> Boolean visit(HavocStmt<DeclType> stmt, Void param) {
        return containsClockVar(stmt);
    }

    @Override
    public Boolean visit(SequenceStmt stmt, Void param) {
        return anyStmtContainsTiming(stmt.getStmts());
    }

    @Override
    public Boolean visit(NonDetStmt stmt, Void param) {
        return anyStmtContainsTiming(stmt.getStmts());
    }

    @Override
    public Boolean visit(OrtStmt stmt, Void param) {
        return anyStmtContainsTiming(stmt.getStmts());
    }

    @Override
    public Boolean visit(LoopStmt stmt, Void param) {
        return stmt.getStmt().accept(this, null);
    }

    @Override
    public Boolean visit(IfStmt stmt, Void param) {
        return Assume(stmt.getCond()).accept(this, null)
                || stmt.getThen().accept(this, null)
                || stmt.getElze().accept(this, null);
    }

    @Override
    public Boolean visit(DelayStmt stmt, Void param) {
        return true;
    }

    @Override
    public Boolean visit(ResetStmt stmt, Void param) {
        return true;
    }

    private boolean containsClockVar(final Stmt stmt) {
        return StmtUtils.getVars(stmt).stream().anyMatch(v -> v.getType() instanceof ClockType);
    }

    private boolean anyStmtContainsTiming(final Collection<Stmt> stmts) {
        return stmts.stream().anyMatch(stmt -> stmt.accept(this, null));
    }
}
