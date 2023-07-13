package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Concretizer;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.Exprs;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import static com.google.common.base.Preconditions.checkNotNull;

public final class IndexedExprConcretizer implements Concretizer<IndexedExprState, BasicExprState> {

    private final Solver solver;
    private final PartialOrd<ExprState> partialOrd;

    private IndexedExprConcretizer(final Solver solver) {
        this.solver = checkNotNull(solver);
        partialOrd = ExprOrd.create(solver);
    }

    public static IndexedExprConcretizer create(final Solver solver) {
        return new IndexedExprConcretizer(solver);
    }

    @Override
    public BasicExprState concretize(IndexedExprState state) {
        final Expr<BoolType> expr = state.toExpr();
        final VarIndexing indexing = state.getVarIndexing();
        final Expr<BoolType> unindexedExpr = removeHighestIndex(expr, indexing);
        return BasicExprState.of(unindexedExpr);
    }

    private <T extends Type> Expr<T> removeHighestIndex(Expr<T> expr, VarIndexing indexing) {
        if (expr instanceof RefExpr) {
            final RefExpr<T> refExpr = (RefExpr<T>) expr;
            final Decl<T> decl = refExpr.getDecl();
            if (decl instanceof IndexedConstDecl) {
                final IndexedConstDecl<T> indexedConstDecl = (IndexedConstDecl<T>) decl;
                final VarDecl<T> varDecl = indexedConstDecl.getVarDecl();
                final int index = indexedConstDecl.getIndex();
                final int highestIndex = indexing.get(varDecl);
                if (index == highestIndex) {
                    return Exprs.Ref(varDecl);
                } else {
                    final String constName = varDecl.getName() + "_const_" + index;
                    final ConstDecl<T> constDecl = Decls.Const(constName, varDecl.getType());
                    return Exprs.Ref(constDecl);
                }
            }
        }
        return expr.map(op -> removeHighestIndex(op, indexing));
    }

    @Override
    public boolean proves(IndexedExprState indexedExprState, BasicExprState exprState) {
        return partialOrd.isLeq(concretize(indexedExprState), exprState);
    }

    @Override
    public boolean inconsistentConcrState(IndexedExprState state) {
        try (WithPushPop wpp = new WithPushPop(solver)) {
            solver.add(state.toExpr());
            return solver.check().isUnsat();
        }
    }
}
