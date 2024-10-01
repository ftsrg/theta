package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

import static com.google.common.base.Preconditions.checkArgument;
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
        final VarDecl<?> varDecl = extractVarDecl(expr);
        return reverse(varDecl, 0);
    }

    private Expr<?> reversePrime(final PrimeExpr<?> expr) {
        final int primeDepth = primeDepth(expr);
        final VarDecl<?> varDecl = extractVarDecl(expr);
        return reverse(varDecl, primeDepth);
    }

    private Expr<?> reverse(final VarDecl<?> decl, int primeDepth) {
        checkArgument(primeDepth > 0 && primeDepth <= indexing.get(decl));
        return Prime(decl.getRef(), indexing.get(decl) - primeDepth);
    }

    private static int primeDepth(final Expr<?> expr) {
        if (expr instanceof PrimeExpr) {
            return 1 + primeDepth(((PrimeExpr<?>) expr).getOp());
        } else {
            return 0;
        }
    }

    private static VarDecl<?> extractVarDecl(final Expr<?> expr) {
        if (expr instanceof RefExpr<?> refExpr) {
            checkArgument(refExpr.getDecl() instanceof VarDecl);
            return (VarDecl<?>) refExpr.getDecl();
        } else if (expr instanceof PrimeExpr<?> primeExpr) {
            return extractVarDecl(primeExpr.getOp());
        } else {
            throw new IllegalArgumentException("Cannot extract variable declaration from expression: " + expr);
        }
    }
}
