package hu.bme.mit.theta.analysis.stmtoptimizer;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class StmtSimplifier {

    public static Stmt simplifyStmt(final Valuation valuation, final Stmt stmt) {
        MutableValuation mutableValuation = MutableValuation.copyOf(valuation);
        final var result = stmt.accept(new StmtSimplifierVisitor(), mutableValuation);
        return result.stmt;
    }

    private enum SimplifyStatus {
        SUCCESS, BOTTOM
    }

    private static class SimplifyResult {

        private final Stmt stmt;
        private final SimplifyStatus status;

        public static SimplifyResult of(final Stmt stmt, final SimplifyStatus status) {
            return new SimplifyResult(stmt, status);
        }

        private SimplifyResult(final Stmt stmt, final SimplifyStatus status) {
            this.stmt = stmt;
            this.status = status;
        }
    }

    private static class StmtSimplifierVisitor implements StmtVisitor<MutableValuation, SimplifyResult> {

        @Override
        public SimplifyResult visit(final SkipStmt stmt, final MutableValuation valuation) {
            return SimplifyResult.of(SkipStmt.getInstance(), SimplifyStatus.SUCCESS);
        }

        @Override
        public SimplifyResult visit(final AssumeStmt stmt, final MutableValuation valuation) {
            final Expr<BoolType> simplifiedExpr = ExprUtils.simplify(stmt.getCond(), valuation);
            final Stmt simplifiedStmt = AssumeStmt.of(simplifiedExpr);
            if (simplifiedExpr instanceof BoolLitExpr) {
                final BoolLitExpr condLit = (BoolLitExpr) simplifiedExpr;
                if (!condLit.getValue()) {
                    return SimplifyResult.of(simplifiedStmt, SimplifyStatus.BOTTOM);
                }
            }
            return SimplifyResult.of(simplifiedStmt, SimplifyStatus.SUCCESS);
        }

        @Override
        public <DeclType extends Type> SimplifyResult visit(final AssignStmt<DeclType> stmt, final MutableValuation valuation) {
            final VarDecl<DeclType> varDecl = stmt.getVarDecl();
            final Expr<DeclType> expr = ExprUtils.simplify(stmt.getExpr(), valuation);
            if (expr instanceof LitExpr<?>) {
                final LitExpr<?> lit = (LitExpr<?>) expr;
                valuation.put(varDecl, lit);
            } else {
                valuation.remove(varDecl);
            }
            return SimplifyResult.of(AssignStmt.of(varDecl, expr), SimplifyStatus.SUCCESS);
        }

        @Override
        public <DeclType extends Type> SimplifyResult visit(final HavocStmt<DeclType> stmt, final MutableValuation valuation) {
            final VarDecl<?> varDecl = stmt.getVarDecl();
            valuation.remove(varDecl);
            return SimplifyResult.of(stmt, SimplifyStatus.SUCCESS);
        }

        @Override
        public SimplifyResult visit(final SequenceStmt stmt, final MutableValuation valuation) {
            final var subStmtsUnrolled = stmt.getStmts().stream()
                    .map(subStmt -> subStmt.accept(this, valuation)).collect(Collectors.toList());
            final var simplifiedStmt = SequenceStmt.of(subStmtsUnrolled.stream().map(result -> result.stmt)
                    .collect(Collectors.toList()));
            final boolean anyBottom = subStmtsUnrolled.stream().anyMatch(result -> result.status == SimplifyStatus.BOTTOM);
            if (anyBottom) {
                return SimplifyResult.of(AssumeStmt.of(False()), SimplifyStatus.BOTTOM);
            } else {
                return SimplifyResult.of(simplifiedStmt, SimplifyStatus.SUCCESS);
            }
        }

        @Override
        public SimplifyResult visit(final NonDetStmt stmt, final MutableValuation valuation) {
            final List<MutableValuation> valuations = new ArrayList<>();
            final List<Stmt> successfulSubStmts = new ArrayList<>();
            for (int i = 0; i < stmt.getStmts().size(); i++) {
                final MutableValuation subVal = MutableValuation.copyOf(valuation);
                final SimplifyResult result = stmt.getStmts().get(i).accept(this, subVal);
                if (result.status == SimplifyStatus.SUCCESS) {
                    valuations.add(subVal);
                    successfulSubStmts.add(result.stmt);
                }
            }
            if (successfulSubStmts.size() == 0) {
                return SimplifyResult.of(AssumeStmt.of(False()), SimplifyStatus.BOTTOM);
            } else if (successfulSubStmts.size() == 1) {
                successfulSubStmts.get(0).accept(this, valuation);
                return SimplifyResult.of(successfulSubStmts.get(0), SimplifyStatus.SUCCESS);
            } else {
                successfulSubStmts.get(0).accept(this, valuation);
                List<Decl<?>> toRemove = new ArrayList<>();
                for (Decl<?> decl : valuation.getDecls()) {
                    for (MutableValuation subVal : valuations) {
                        if (!valuation.eval(decl).equals(subVal.eval(decl))) {
                            toRemove.add(decl);
                            break;
                        }
                    }
                }
                for (Decl<?> decl : toRemove) valuation.remove(decl);
                return SimplifyResult.of(NonDetStmt.of(successfulSubStmts), SimplifyStatus.SUCCESS);
            }

        }

        @Override
        public SimplifyResult visit(final OrtStmt stmt, final MutableValuation valuation) {
            throw new UnsupportedOperationException();
        }

        @Override
        public SimplifyResult visit(final LoopStmt stmt, final MutableValuation valuation) {
            var from = stmt.getFrom();
            var to = stmt.getTo();
            var fromUnrolled = ExprUtils.simplify(from, valuation);
            var toUnrolled = ExprUtils.simplify(to, valuation);
            if (fromUnrolled instanceof IntLitExpr && toUnrolled instanceof IntLitExpr) {
                var fromValue = ((IntLitExpr) fromUnrolled).getValue();
                var toValue = ((IntLitExpr) toUnrolled).getValue();
                var stmts = new ArrayList<Stmt>();
                for (BigInteger bi = fromValue; bi.compareTo(toValue) < 0; bi = bi.add(BigInteger.ONE)) {
                    var assignToLoopVar = AssignStmt.of(stmt.getLoopVariable(), Int(bi));
                    var loopVarIncAndSubStmt = SequenceStmt.of(ImmutableList.of(assignToLoopVar, stmt.getStmt()));
                    var result = loopVarIncAndSubStmt.accept(this, valuation);
                    if (result.status == SimplifyStatus.SUCCESS) {
                        stmts.add(result.stmt);
                    } else {
                        return SimplifyResult.of(AssumeStmt.of(False()), SimplifyStatus.BOTTOM);
                    }

                }
                return SimplifyResult.of(SequenceStmt.of(stmts), SimplifyStatus.SUCCESS);
            }
            throw new IllegalArgumentException(String.format("Couldn't unroll loop statement %s", stmt));
        }

        @Override
        public <DeclType extends Type> SimplifyResult visit(PushStmt<DeclType> stmt, MutableValuation param) {
            throw new UnsupportedOperationException();
        }

        @Override
        public <DeclType extends Type> SimplifyResult visit(PopStmt<DeclType> stmt, MutableValuation param) {
            throw new UnsupportedOperationException();
        }
        public SimplifyResult visit(IfStmt stmt, MutableValuation valuation) {
            final Expr<BoolType> cond = ExprUtils.simplify(stmt.getCond(), valuation);

            if (cond instanceof BoolLitExpr) {
                final BoolLitExpr condLit = (BoolLitExpr) cond;
                if (condLit.getValue()) {
                    return stmt.getThen().accept(this, valuation);
                } else {
                    return stmt.getElze().accept(this, valuation);
                }
            } else {
                final MutableValuation thenVal = MutableValuation.copyOf(valuation);
                final MutableValuation elzeVal = MutableValuation.copyOf(valuation);

                final SimplifyResult thenResult = stmt.getThen().accept(this, thenVal);
                final SimplifyResult elzeResult = stmt.getElze().accept(this, elzeVal);

                if (thenResult.status == SimplifyStatus.BOTTOM && elzeResult.status == SimplifyStatus.BOTTOM) {
                    return SimplifyResult.of(AssumeStmt.of(False()), SimplifyStatus.BOTTOM);
                }

                if (thenResult.status == SimplifyStatus.SUCCESS && elzeResult.status == SimplifyStatus.BOTTOM) {
                    final AssumeStmt assume = AssumeStmt.of(cond);
                    final SequenceStmt assumeAndThen = SequenceStmt.of(ImmutableList.of(assume,stmt.getThen()));
                    return assumeAndThen.accept(this, valuation);
                }

                if (thenResult.status == SimplifyStatus.BOTTOM && elzeResult.status == SimplifyStatus.SUCCESS) {
                    final AssumeStmt assumeNot = AssumeStmt.of(Not(cond));
                    final SequenceStmt assumeAndElze = SequenceStmt.of(ImmutableList.of(assumeNot,stmt.getElze()));
                    return assumeAndElze.accept(this, valuation);
                }

                stmt.getThen().accept(this, valuation);
                var toRemove = valuation.getDecls().stream()
                        .filter(it -> !valuation.eval(it).equals(elzeVal.eval(it)))
                        .collect(Collectors.toSet());
                for (Decl<?> decl : toRemove) valuation.remove(decl);
                return SimplifyResult.of(IfStmt.of(cond, thenResult.stmt, elzeResult.stmt), SimplifyStatus.SUCCESS);
            }
        }
    }

}
