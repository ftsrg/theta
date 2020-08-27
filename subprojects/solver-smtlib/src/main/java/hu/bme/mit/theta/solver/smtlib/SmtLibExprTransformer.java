package hu.bme.mit.theta.solver.smtlib;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.core.type.Expr;

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
                .build();
    }

    public final String toTerm(final Expr<?> expr) {
        try {
            return exprToTerm.get(expr, () -> table.dispatch(expr));
        } catch (final ExecutionException e) {
            throw new AssertionError();
        }
    }

}
