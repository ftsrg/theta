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
package hu.bme.mit.theta.core.type.anytype;

import static com.google.common.base.Preconditions.checkArgument;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class Exprs {

	private Exprs() {
	}

	public static <DeclType extends Type> RefExpr<DeclType> Ref(final Decl<DeclType> decl) {
		return new RefExpr<>(decl);
	}

	public static <ExprType extends Type> IteExpr<ExprType> Ite(final Expr<BoolType> cond, final Expr<ExprType> then,
			final Expr<ExprType> elze) {
		return new IteExpr<>(cond, then, elze);
	}

	public static <ExprType extends Type> PrimeExpr<ExprType> Prime(final Expr<ExprType> op) {
		return new PrimeExpr<>(op);
	}

	/*
	 * Convenience methods
	 */

	public static <ExprType extends Type> PrimeExpr<ExprType> Prime(final Expr<ExprType> op, final int i) {
		checkArgument(i > 0);
		if (i == 1) {
			return Prime(op);
		} else {
			return Prime(Prime(op, i - 1));
		}
	}

}
