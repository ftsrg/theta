package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Set;

public class AtomCollector {

    public static Set<Expr<BoolType>> collectAtoms(final Stmt stmt){
        final Set<Expr<BoolType>> atoms = Containers.createSet();
        stmt.accept(new AllAssumesCollector(), atoms);
        return atoms;
    }

    private static class AllAssumesCollector implements StmtVisitor<Set<Expr<BoolType>>, Void> {

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
        public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, Set<Expr<BoolType>> atoms) {
            return null;
        }

        @Override
        public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, Set<Expr<BoolType>> atoms) {
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
    }

}
