/*
 *  Copyright 2024 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.core.utils;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;

import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.common.DispatchTable2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

public class ExprReverser {

    private final VarIndexing indexing;

    private final DispatchTable<Expr<?>> TABLE =
            DispatchTable.<Expr<?>>builder()
                    .addCase(RefExpr.class, this::reverseRef)
                    .addCase(PrimeExpr.class, this::reversePrime)

                    // Default

                    .addDefault(
                            (o) -> {
                                final Expr<?> expr = (Expr<?>) o;
                                return expr.map(e -> reverseInner(e));
                            })
                    .build();

    public ExprReverser(VarIndexing indexing) {
        this.indexing = indexing;
    }

    public <T extends Type> Expr<T> reverse(final Expr<T> expr) {
        final var transformed = PrimeToLeaves.transform(expr);
        return (Expr<T>) TABLE.dispatch(transformed);
    }

    @SuppressWarnings("unchecked")
    private <T extends Type> Expr<T> reverseInner(final Expr<T> expr) {
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
        checkArgument(primeDepth >= 0 && primeDepth <= indexing.get(decl));
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
            throw new IllegalArgumentException(
                    "Cannot extract variable declaration from expression: " + expr);
        }
    }

    private static class PrimeToLeaves {

        private static final DispatchTable2<Integer, Expr<?>> TABLE =
                DispatchTable2.<Integer, Expr<?>>builder()
                        .addCase(RefExpr.class, PrimeToLeaves::transformRef)
                        .addCase(PrimeExpr.class, PrimeToLeaves::transformPrime)

                        // Default

                        .addDefault(
                                (o, primeDepth) -> {
                                    final Expr<?> expr = (Expr<?>) o;
                                    return expr.map(e -> transform(e, primeDepth));
                                })
                        .build();

        public static <T extends Type> Expr<T> transform(final Expr<T> expr) {
            return transform(expr, 0);
        }

        @SuppressWarnings("unchecked")
        private static <T extends Type> Expr<T> transform(final Expr<T> expr, int primeDepth) {
            return (Expr<T>) TABLE.dispatch(expr, primeDepth);
        }

        private static Expr<?> transformRef(final Expr<?> expr, Integer primeDepth) {
            return Prime(expr, primeDepth);
        }

        private static Expr<?> transformPrime(final Expr<?> expr, Integer primeDepth) {
            return transform(((PrimeExpr<?>) expr).getOp(), primeDepth + 1);
        }
    }
}
