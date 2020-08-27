package hu.bme.mit.theta.solver.smtlib;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

import java.util.concurrent.ExecutionException;

public class SmtLibExprTransformer {
    private static final int CACHE_SIZE = 1000;

    private final SmtLibTransformationManager transformer;

    private final Cache<Expr<?>, String> exprToTerm;
    private final DispatchTable<String> table;
    private final Env env;

    public SmtLibExprTransformer(final SmtLibTransformationManager transformer) {
        this.transformer = transformer;
        this.env = new Env();

        this.exprToTerm = CacheBuilder.newBuilder().maximumSize(CACHE_SIZE).build();

        this.table = DispatchTable.<String>builder()

                // General

                .addCase(RefExpr.class, this::transformRef)

                .addCase(IteExpr.class, this::transformIte)

                .build();
    }

    public final String toTerm(final Expr<?> expr) {
        try {
            return exprToTerm.get(expr, () -> table.dispatch(expr));
        } catch (final ExecutionException e) {
            throw new AssertionError();
        }
    }

    ////

    /*
     * General
     */

    protected String transformRef(final RefExpr<?> expr) {
        final Decl<?> decl = expr.getDecl();
        if (decl instanceof ConstDecl) {
            return transformer.toSymbol(decl);
        } else if (decl instanceof ParamDecl) {
            return (String) env.eval(DeclSymbol.of(decl));
        } else {
            throw new UnsupportedOperationException("Cannot transform reference for declaration: " + decl);
        }
    }

    protected String transformIte(final IteExpr<?> expr) {
        final String condTerm = toTerm(expr.getCond());
        final String thenTerm = toTerm(expr.getThen());
        final String elzeTerm = toTerm(expr.getElse());
        return String.format("(ite %s %s %s)", condTerm, thenTerm, elzeTerm);
    }
}
