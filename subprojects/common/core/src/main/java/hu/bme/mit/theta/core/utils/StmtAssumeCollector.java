package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.IfStmt;
import hu.bme.mit.theta.core.stmt.LoopStmt;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.OrtStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.Set;

public class StmtAssumeCollector {

    public static Set<Expr<BoolType>> collectAssumes(final Stmt stmt) {
        final Set<Expr<BoolType>> assigns = Containers.createSet();
        stmt.accept(new StmtAssumeCollector.AllAssumesCollector(), assigns);
        return assigns;
    }

    private static class AllAssumesCollector implements
        StmtVisitor<Set<Expr<BoolType>>, Void> {

        @Override
        public Void visit(SkipStmt stmt, Set<Expr<BoolType>> atoms) {
            return null;
        }

        @Override
        public Void visit(AssumeStmt stmt, Set<Expr<BoolType>> atoms) {
            atoms.addAll(ExprUtils.getAtoms(stmt.getCond()));
            return null;
        }

        @Override
        public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt,
            Set<Expr<BoolType>> atoms) {
            return null;
        }

        @Override
        public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt,
            Set<Expr<BoolType>> atoms) {
            return null;
        }

        @Override
        public Void visit(SequenceStmt stmt, Set<Expr<BoolType>> atoms) {
            stmt.getStmts().forEach(s -> s.accept(this, atoms));
            return null;
        }

        @Override
        public Void visit(NonDetStmt stmt, Set<Expr<BoolType>> atoms) {
            stmt.getStmts().forEach(s -> s.accept(this, atoms));
            return null;
        }

        @Override
        public Void visit(OrtStmt stmt, Set<Expr<BoolType>> atoms) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Void visit(LoopStmt stmt, Set<Expr<BoolType>> atoms) {
            stmt.getStmt().accept(this, atoms);
            return null;
        }

        public Void visit(IfStmt stmt, Set<Expr<BoolType>> atoms) {
            stmt.getThen().accept(this, atoms);
            stmt.getElze().accept(this, atoms);
            atoms.addAll(ExprUtils.getAtoms(stmt.getCond()));
            return null;
        }
    }
}
