package hu.bme.mit.theta.core.clock.impl;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.Ordered;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.clocktype.ClockConstraintExpr;
import hu.bme.mit.theta.core.type.clocktype.ClockDiffExpr;
import hu.bme.mit.theta.core.type.clocktype.ClockType;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static java.util.stream.Collectors.toList;

public abstract class ClockImpl<CType extends Ordered<CType>> {

    private final HashMap<Decl<ClockType>, VarDecl<CType>> clockLut;
    private Stmt delayStmt;

    protected ClockImpl(final Collection<VarDecl<ClockType>> clocks) {
        checkNotNull(clocks);
        clockLut = new HashMap<>();
        for (VarDecl<ClockType> clock : clocks) {
            final VarDecl<CType> newVar = Decls.Var(clock.getName(), type());
            clockLut.put(clock, newVar);
        }
    }

    protected abstract CType type();

    protected abstract Expr<CType> addExpr(final Expr<CType> leftOp, final Expr<CType> rightOp);

    protected abstract Expr<CType> subExpr(final Expr<CType> leftOp, final Expr<CType> rightOp);

    public VarDecl<CType> transformVar(final VarDecl<ClockType> clockVar) {
        return clockLut.get(clockVar);
    }

    public <EType extends Type> Expr<EType> transformExpr(final Expr<EType> expr) {
        if (expr instanceof ClockConstraintExpr) {
            return (Expr<EType>) createRelExpr((ClockConstraintExpr) expr);
        }
        return expr.map(this::transformExpr);
    }

    public Stmt transformStmt(final Stmt stmt) {
        return stmt.accept(new StmtVisitor<Void, Stmt>() {
            @Override
            public Stmt visit(SkipStmt stmt, Void param) {
                return stmt;
            }

            @Override
            public Stmt visit(AssumeStmt stmt, Void param) {
                return AssumeStmt.of(transformExpr(stmt.getCond()));
            }

            @Override
            public <DeclType extends Type> Stmt visit(AssignStmt<DeclType> stmt, Void param) {
                assert !(stmt.getVarDecl().getType() instanceof ClockType);
                return stmt;
            }

            @Override
            public <DeclType extends Type> Stmt visit(HavocStmt<DeclType> stmt, Void param) {
                assert !(stmt.getVarDecl().getType() instanceof ClockType);
                return stmt;
            }

            @Override
            public Stmt visit(SequenceStmt stmt, Void param) {
                return SequenceStmt.of(visitStmts(stmt.getStmts()));
            }

            @Override
            public Stmt visit(NonDetStmt stmt, Void param) {
                return NonDetStmt.of(visitStmts(stmt.getStmts()));
            }

            @Override
            public Stmt visit(OrtStmt stmt, Void param) {
                return OrtStmt.of(visitStmts(stmt.getStmts()));
            }

            @Override
            public Stmt visit(LoopStmt stmt, Void param) {
                final Stmt newStmt = stmt.getStmt().accept(this, null);
                return LoopStmt.of(newStmt, stmt.getLoopVariable(), stmt.getFrom(), stmt.getTo());
            }

            @Override
            public Stmt visit(IfStmt stmt, Void param) {
                final Expr<BoolType> newCond = transformExpr(stmt.getCond());
                final Stmt newThen = stmt.getThen().accept(this, null);
                final Stmt newElze = stmt.getElze().accept(this, null);
                return IfStmt.of(newCond, newThen, newElze);
            }

            @Override
            public Stmt visit(DelayStmt stmt, Void param) {
                if (delayStmt == null) {
                    final List<Stmt> stmts = new ArrayList<>();

                    final VarDecl<CType> delayVar = Decls.Var("__delay", type());
                    stmts.add(HavocStmt.of(delayVar));

                    final Expr<IntType> intZeroExpr = Int(0);
                    final Expr<CType> tZeroExpr = IntType.getInstance().Cast(intZeroExpr, type());
                    stmts.add(AssumeStmt.of(type().Geq(delayVar.getRef(), tZeroExpr)));

                    for (Decl<ClockType> clock : clockLut.keySet()) {
                        final VarDecl<CType> replacementVar = clockLut.get(clock);
                        final Expr<CType> addDelayExpr = addExpr(replacementVar.getRef(), delayVar.getRef());
                        stmts.add(AssignStmt.of(replacementVar, addDelayExpr));
                    }

                    delayStmt = SequenceStmt.of(stmts);
                }
                return delayStmt;
            }

            @Override
            public Stmt visit(ResetStmt stmt, Void param) {
                final VarDecl<ClockType> clockVar = stmt.getClockDecl();
                final VarDecl<CType> tVar = clockLut.get(clockVar);

                final Expr<IntType> intValueExpr = Int(stmt.getValue());
                final Expr<CType> tValueExpr = IntType.getInstance().Cast(intValueExpr, type());

                return AssignStmt.of(tVar, tValueExpr);
            }

            private List<Stmt> visitStmts(final List<Stmt> stmts) {
                return stmts.stream().map(stmt -> stmt.accept(this, null)).collect(toList());
            }
        }, null);
    }

    private Expr<BoolType> createRelExpr(ClockConstraintExpr clockConstraintExpr) {
        final Expr<ClockType> clockExpr = clockConstraintExpr.getLeftOp();
        final Expr<IntType> value = clockConstraintExpr.getRightOp();

        final Expr<CType> tClockExpr = transformClocks(clockExpr);
        final Expr<CType> tValue = IntType.getInstance().Cast(value, type());

        switch (clockConstraintExpr.getRel()) {
            case LT:
                return type().Lt(tClockExpr, tValue);
            case LEQ:
                return type().Leq(tClockExpr, tValue);
            case GT:
                return type().Gt(tClockExpr, tValue);
            case GEQ:
                return type().Geq(tClockExpr, tValue);
            case EQ:
                return And(type().Leq(tClockExpr, tValue), type().Geq(tClockExpr, tValue));
            default:
                throw new UnsupportedOperationException();
        }
    }

    private Expr<CType> transformClocks(final Expr<ClockType> expr) {
        if (expr instanceof RefExpr) {
            final RefExpr<ClockType> clockRefExpr = (RefExpr<ClockType>) expr;
            return RefExpr.of(clockLut.get(clockRefExpr.getDecl()));

        } else if (expr instanceof ClockDiffExpr) {
            final ClockDiffExpr clockDiffExpr = (ClockDiffExpr) expr;
            final Expr<CType> leftOp = transformClocks(clockDiffExpr.getLeftOp());
            final Expr<CType> rightOp = transformClocks(clockDiffExpr.getRightOp());
            return subExpr(leftOp, rightOp);

        } else {
            throw new AssertionError();
        }
    }
}
