package hu.bme.mit.theta.analysis.utils;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class StmtUnroller {

    public static Stmt unrollStmt(final Valuation valuation, final Stmt stmt) {
        MutableValuation mutableValuation = MutableValuation.copyOf(valuation);
        return stmt.accept(new StmtUnrollerVisitor(),mutableValuation);
    }

    private static class StmtUnrollerVisitor implements StmtVisitor<MutableValuation, Stmt> {

        @Override
        public Stmt visit(final SkipStmt stmt, final MutableValuation valuation) {
            return SkipStmt.getInstance();
        }

        @Override
        public Stmt visit(final AssumeStmt stmt, final MutableValuation valuation) {
            var result = StmtApplier.apply(stmt,valuation,true);
            return stmt;
        }

        @Override
        public <DeclType extends Type> Stmt visit(final AssignStmt<DeclType> stmt, final MutableValuation valuation) {
            var result = StmtApplier.apply(stmt,valuation,true);
            return stmt;
        }

        @Override
        public <DeclType extends Type> Stmt visit(final HavocStmt<DeclType> stmt, final MutableValuation valuation) {
            var result = StmtApplier.apply(stmt,valuation,true);
            return stmt;
        }

        @Override
        public Stmt visit(final SequenceStmt stmt, final MutableValuation valuation) {
            var subStmtsUnrolled = stmt.getStmts().stream()
                    .map(subStmt -> subStmt.accept(this,valuation))
                    .collect(Collectors.toList());
            return SequenceStmt.of(subStmtsUnrolled);
        }

        @Override
        public Stmt visit(final NonDetStmt stmt, final MutableValuation valuation) {
            List<MutableValuation> valuations = new ArrayList<>();
            List<Stmt> subStmtsUnrolled = new ArrayList<>();
            for (int i = 0; i < stmt.getStmts().size(); i++) {
                MutableValuation subVal = MutableValuation.copyOf(valuation);
                Stmt subStmtUnrolled = stmt.getStmts().get(i).accept(this,subVal);
                valuations.add(subVal);
                subStmtsUnrolled.add(subStmtUnrolled);
            }
            stmt.getStmts().get(0).accept(this,valuation);
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
            return NonDetStmt.of(subStmtsUnrolled);
        }

        @Override
        public Stmt visit(final OrtStmt stmt, final MutableValuation valuation) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Stmt visit(final LoopStmt stmt, final MutableValuation valuation) {
            var iterations = stmt.getIterations();
            var iterationsUnrolled = ExprUtils.simplify(iterations,valuation);
            if(iterationsUnrolled instanceof IntLitExpr){
                var numberOfIterations = ((IntLitExpr) iterationsUnrolled).getValue();
                var stmts = new ArrayList<Stmt>();
                for (BigInteger bi = BigInteger.valueOf(0); bi.compareTo(numberOfIterations) < 0; bi = bi.add(BigInteger.ONE)) {
                    var subStmtUnrolled = stmt.getStmt().accept(this,valuation);
                    stmts.add(subStmtUnrolled);
                }
                return SequenceStmt.of(stmts);
            }
            throw new IllegalArgumentException(String.format("Couldn't unroll loop statement %s", stmt));
        }
    }

}
