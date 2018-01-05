/*
 *  Copyright 2017 Budapest University of Technology and Economics
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

import java.util.List;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

final class PrimeCounter {

	private PrimeCounter() {
	}

	static VarIndexing countPrimes(final Expr<?> expr) {
		return collectPrimes(expr, 0).build();
	}

	private static VarIndexing.Builder collectPrimes(final Expr<?> expr, final int nPrimes) {
		if (expr instanceof RefExpr) {
			final RefExpr<?> ref = (RefExpr<?>) expr;
			final Decl<?> decl = ref.getDecl();
			if (decl instanceof VarDecl) {
				final VarDecl<?> var = (VarDecl<?>) decl;
				return VarIndexing.builder(0).inc(var, nPrimes);
			}
		}

		if (expr instanceof PrimeExpr<?>) {
			final PrimeExpr<?> primeExpr = (PrimeExpr<?>) expr;
			final Expr<?> op = primeExpr.getOp();
			return collectPrimes(op, nPrimes + 1);
		}

		final List<? extends Expr<?>> ops = expr.getOps();
		return ops.stream().map(op -> collectPrimes(op, nPrimes)).reduce(VarIndexing.builder(0),
				VarIndexing.Builder::join);
	}

}
