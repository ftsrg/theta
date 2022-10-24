package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.java.mdd.MddCanonizationStrategy;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;

import java.util.function.Function;
import java.util.function.Supplier;

public class MddExpressionTemplate implements MddNode.Template {

    private final Expr<BoolType> expr;
    private final Function<Object, VarDecl> extractVar;
    private final Supplier<Solver> solverSupplier;

    private MddExpressionTemplate(Expr<BoolType> expr, Function<Object, VarDecl> extractVar, Supplier<Solver> solverSupplier){
        this.expr = expr;
        this.extractVar = extractVar;
        this.solverSupplier = solverSupplier;
    }

    public static MddExpressionTemplate of(Expr<BoolType> expr, Function<Object, VarDecl> extractVar, Supplier<Solver> solverSupplier) {
        return new MddExpressionTemplate(expr, extractVar, solverSupplier);
    }

    @Override
    public RecursiveIntObjMapView<? extends MddNode> toCanonicalRepresentation(MddVariable mddVariable, MddCanonizationStrategy mddCanonizationStrategy) {
        final VarDecl decl = extractVar.apply(mddVariable.getTraceInfo());

        // Check if default
        if(!ExprUtils.getConstants(expr).contains(decl)){
            final MddNode childNode = mddVariable.checkInNode(new MddExpressionTemplate(expr, o -> (VarDecl) o, solverSupplier));
            return MddExpressionRepresentation.ofDefault(expr, decl, mddVariable, solverSupplier, childNode);
        }

        return MddExpressionRepresentation.of(expr, decl, mddVariable, solverSupplier);

    }
}
