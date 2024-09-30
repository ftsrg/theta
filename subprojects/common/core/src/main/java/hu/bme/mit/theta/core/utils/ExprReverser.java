package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;

public class ExprReverser {

    private final VarIndexing indexing;

    private final DispatchTable<Expr<?>> TABLE = DispatchTable.<Expr<?>>builder()

            .addCase(RefExpr.class, this::reverseRef)

            .addCase(PrimeExpr.class, this::reversePrime)

            // Default

            .addDefault((o) -> {
                final Expr<?> expr = (Expr<?>) o;
                return expr.map(e -> reverse(e));
            })

            .build();

    public ExprReverser(VarIndexing indexing) {
        this.indexing = indexing;
    }

    @SuppressWarnings("unchecked")
    public <T extends Type> Expr<T> reverse(final Expr<T> expr) {
        return (Expr<T>) TABLE.dispatch(expr);
    }

    /*
     * General
     */

    private Expr<?> reverseRef(final RefExpr<?> expr) {
        return Prime(expr);
    }

    private Expr<?> reversePrime(final PrimeExpr<?> expr) {
        return expr.getOp();
    }
}
