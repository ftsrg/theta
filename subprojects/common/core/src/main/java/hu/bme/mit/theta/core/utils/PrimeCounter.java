/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.utils.indexings.BasicVarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;

public final class PrimeCounter {

    private PrimeCounter() {}

    public static VarIndexing countPrimes(final Expr<?> expr) {
        final BasicVarIndexing.BasicVarIndexingBuilder builder =
                VarIndexingFactory.basicIndexingBuilder(0);
        collectPrimes(expr, 0, builder);
        return builder.build();
    }

    // Accumulates into a single builder: joining per-operand builders copies the whole map for
    // every operand, which is quadratic on large flat conjunctions.
    private static void collectPrimes(
            final Expr<?> expr,
            final int nPrimes,
            final BasicVarIndexing.BasicVarIndexingBuilder builder) {
        if (expr instanceof RefExpr) {
            final RefExpr<?> ref = (RefExpr<?>) expr;
            final Decl<?> decl = ref.getDecl();
            if (decl instanceof VarDecl) {
                final VarDecl<?> varDecl = (VarDecl<?>) decl;
                final int current = builder.get(varDecl);
                if (nPrimes > current) {
                    builder.inc(varDecl, nPrimes - current);
                }
                return;
            }
        }

        if (expr instanceof PrimeExpr<?>) {
            final PrimeExpr<?> primeExpr = (PrimeExpr<?>) expr;
            final Expr<?> op = primeExpr.getOp();
            collectPrimes(op, nPrimes + 1, builder);
            return;
        }

        for (final Expr<?> op : expr.getOps()) {
            collectPrimes(op, nPrimes, builder);
        }
    }
}
