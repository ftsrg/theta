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

import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

final class ExprPrimeApplier {

	private ExprPrimeApplier() {
	}

	static <T extends Type> Expr<T> applyPrimes(final Expr<T> expr, final VarIndexing indexing) {
		if (expr instanceof RefExpr) {
			final RefExpr<T> ref = (RefExpr<T>) expr;
			final Decl<T> decl = ref.getDecl();
			if (decl instanceof VarDecl) {
				final VarDecl<T> varDecl = (VarDecl<T>) decl;
				final int index = indexing.get(varDecl);
				if (index == 0) {
					return expr;
				} else {
					return Prime(expr, index);
				}
			}
		}

		return expr.map(op -> applyPrimes(op, indexing));
	}

}
