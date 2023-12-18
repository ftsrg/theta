package hu.bme.mit.theta.analysis.zone;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.clock.constr.ClockConstrs;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.clocktype.ClockConstraintExpr;
import hu.bme.mit.theta.core.type.clocktype.ClockType;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.List;

public class ZoneStmtApplier {

    private static final ZonePostStmtVisitor POST_VISITOR = new ZonePostStmtVisitor();
    private static final ZonePreStmtVisitor PRE_VISITOR = new ZonePreStmtVisitor();

    private ZoneStmtApplier() {
    }

    public static ZoneState post(final ZoneState state, final StmtAction action, ZonePrec prec) {
        final ZoneState.Builder builder = state.project(prec.getVars());
        final List<Stmt> stmts = action.getStmts();
        for (final Stmt stmt : stmts) {
            stmt.accept(POST_VISITOR, builder);
        }
        return builder.build();
    }

    public static ZoneState pre(final ZoneState state, final StmtAction action, ZonePrec prec) {
        final ZoneState.Builder builder = state.project(prec.getVars());
        final List<Stmt> stmts = Lists.reverse(action.getStmts());
        for (final Stmt stmt : stmts) {
            stmt.accept(PRE_VISITOR, builder);
        }
        return builder.build();
    }

    ///

    private static class ZonePostStmtVisitor implements StmtVisitor<ZoneState.Builder, Void> {

        private ZonePostStmtVisitor() {
        }

        @Override
        public Void visit(SkipStmt stmt, ZoneState.Builder builder) {
            return null;
        }

        @Override
        public Void visit(AssumeStmt stmt, ZoneState.Builder builder) {
            applyAssume(stmt, builder);
            return null;
        }

        @Override
        public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, ZoneState.Builder builder) {
            throw new UnsupportedOperationException();
        }

        @Override
        public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, ZoneState.Builder builder) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Void visit(SequenceStmt stmt, ZoneState.Builder builder) {
            stmt.getStmts().forEach(subStmt -> subStmt.accept(this, builder));
            return null;
        }

        @Override
        public Void visit(NonDetStmt stmt, ZoneState.Builder builder) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Void visit(OrtStmt stmt, ZoneState.Builder builder) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Void visit(LoopStmt stmt, ZoneState.Builder builder) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Void visit(IfStmt stmt, ZoneState.Builder builder) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Void visit(DelayStmt stmt, ZoneState.Builder builder) {
            builder.nonnegative();
            builder.up();
            return null;
        }

        @Override
        public Void visit(ResetStmt stmt, ZoneState.Builder builder) {
            builder.reset(stmt.getClockDecl(), stmt.getValue());
            return null;
        }
    }

    ///

    private static class ZonePreStmtVisitor implements StmtVisitor<ZoneState.Builder, Void> {

        private ZonePreStmtVisitor() {
        }

        @Override
        public Void visit(SkipStmt stmt, ZoneState.Builder builder) {
            return null;
        }

        @Override
        public Void visit(AssumeStmt stmt, ZoneState.Builder builder) {
            applyAssume(stmt, builder);
            return null;
        }

        @Override
        public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, ZoneState.Builder builder) {
            throw new UnsupportedOperationException();
        }

        @Override
        public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, ZoneState.Builder builder) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Void visit(SequenceStmt stmt, ZoneState.Builder builder) {
            Lists.reverse(stmt.getStmts()).forEach(subStmt -> subStmt.accept(this, builder));
            return null;
        }

        @Override
        public Void visit(NonDetStmt stmt, ZoneState.Builder builder) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Void visit(OrtStmt stmt, ZoneState.Builder builder) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Void visit(LoopStmt stmt, ZoneState.Builder builder) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Void visit(IfStmt stmt, ZoneState.Builder builder) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Void visit(DelayStmt stmt, ZoneState.Builder builder) {
            builder.down();
            builder.nonnegative();
            return null;
        }

        @Override
        public Void visit(ResetStmt stmt, ZoneState.Builder builder) {
            final VarDecl<ClockType> clock = stmt.getClockDecl();
            final int value = stmt.getValue();
            builder.and(ClockConstrs.Eq(clock, value));
            builder.free(clock);
            return null;
        }
    }

    ///

    private static void applyAssume(AssumeStmt stmt, ZoneState.Builder builder) {
        ExprUtils.getConjuncts(stmt.getCond()).stream()
                .filter(cond -> cond instanceof ClockConstraintExpr)
                .map(cond -> ClockConstrs.fromClockExpr((ClockConstraintExpr) cond))
                .forEach(builder::and);
    }
}
