package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.java.mdd.MddCanonizationStrategy;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.SolverPool;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.function.Function;
import java.util.function.Supplier;

public class MddExpressionTemplate implements MddNode.Template {

    private final Expr<BoolType> expr;
    private final Function<Object, Decl> extractDecl;
    private final SolverPool solverPool;

    private static Solver lazySolver;

    private static boolean isSat(Expr<BoolType> expr, SolverPool solverPool) {
        if (lazySolver == null) lazySolver = solverPool.requestSolver();
        boolean res;
        try (var wpp = new WithPushPop(lazySolver)) {
            lazySolver.add(expr);
            res = lazySolver.check().isSat();
        }
        return res;
    }

    private MddExpressionTemplate(Expr<BoolType> expr, Function<Object, Decl> extractDecl, SolverPool solverPool) {
        this.expr = expr;
        this.extractDecl = extractDecl;
        this.solverPool = solverPool;
    }

    public static MddExpressionTemplate of(Expr<BoolType> expr, Function<Object, Decl> extractDecl, SolverPool solverPool) {
        return new MddExpressionTemplate(expr, extractDecl, solverPool);
    }

    @Override
    public RecursiveIntObjMapView<? extends MddNode> toCanonicalRepresentation(MddVariable mddVariable, MddCanonizationStrategy mddCanonizationStrategy) {
        final Decl decl = extractDecl.apply(mddVariable.getTraceInfo());

        final Expr<BoolType> canonizedExpr = ExprUtils.canonize(ExprUtils.simplify(expr));

        // TODO: we might not need this
        // Check if terminal 1
        if (ExprUtils.getConstants(canonizedExpr).isEmpty()) {
            if (canonizedExpr instanceof FalseExpr) {
                return mddVariable.getMddGraph().getTerminalZeroNode();
            } else {
                final MddGraph<Expr> mddGraph = (MddGraph<Expr>) mddVariable.getMddGraph();
                return mddGraph.getNodeFor(canonizedExpr);
            }
        }

        // Check if default
        if (!ExprUtils.getConstants(canonizedExpr).contains(decl)) {
            if (mddVariable.getLower().isPresent()) {
                final MddNode childNode = mddVariable.getLower().get().checkInNode(new MddExpressionTemplate(canonizedExpr, o -> (Decl) o, solverPool));
                return MddExpressionRepresentation.ofDefault(canonizedExpr, decl, mddVariable, solverPool, childNode);
            }
        }

        // Check if terminal 0
        if (!isSat(canonizedExpr, solverPool)) {
            return mddVariable.getMddGraph().getTerminalZeroNode();
        }

        return MddExpressionRepresentation.of(canonizedExpr, decl, mddVariable, solverPool);

    }
}
