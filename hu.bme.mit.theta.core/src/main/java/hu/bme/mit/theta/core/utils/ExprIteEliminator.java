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

import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

final class ExprIteEliminator {

	private ExprIteEliminator() {
	}

	static <T extends Type> Expr<T> eliminateIte(final Expr<T> expr) {
		return removeIte(propagateIte(expr));
	}

	/*
	 * Helper methods
	 */

	private static <T extends Type> Expr<T> removeIte(final Expr<T> expr) {
		if (expr instanceof IteExpr) {
			final IteExpr<T> iteExpr = (IteExpr<T>) expr;
			if (iteExpr.getType() instanceof BoolType) {
				final Expr<BoolType> cond = removeIte(iteExpr.getCond());
				final Expr<BoolType> then = TypeUtils.cast(removeIte(iteExpr.getThen()), Bool());
				final Expr<BoolType> elze = TypeUtils.cast(removeIte(iteExpr.getElse()), Bool());
				@SuppressWarnings("unchecked")
				final Expr<T> result = (Expr<T>) And(Or(Not(cond), then), Or(cond, elze));
				return result;
			} else {
				return expr;
			}
		} else {
			return expr.map(ExprIteEliminator::removeIte);
		}
	}

	private static <T extends Type> Expr<T> propagateIte(final Expr<T> expr) {
		if (expr instanceof IteExpr) {
			final IteExpr<T> iteExpr = (IteExpr<T>) expr;
			// Apply propagation to operand(s)
			return iteExpr.withThen(propagateIte(iteExpr.getThen())).withElse(propagateIte(iteExpr.getElse()));
		} else {
			// Apply propagation to operand(s) first, then apply pushdown
			return pushIte(expr.map(ExprIteEliminator::propagateIte));
		}
	}

	// Push expression below ITE, e.g.: X + ite(C,T,E) + Y => ite(C,X+T+Y,X+E+Y)
	private static <T extends Type> Expr<T> pushIte(final Expr<T> expr) {
		if (expr instanceof IteExpr) {
			return expr;
		}

		final List<? extends Expr<?>> ops = expr.getOps();

		// Get the first operand that is an ITE
		final Optional<? extends Expr<?>> optIte = ops.stream().filter(op -> op instanceof IteExpr).findFirst();

		// Nothing to do if none of the operands are ITE
		if (!optIte.isPresent()) {
			return expr;
		}

		final IteExpr<?> ite = (IteExpr<?>) optIte.get();

		// Nothing to do if the operand is of bool type
		if (ite.getType() instanceof BoolType) {
			return expr;
		}

		final List<Expr<?>> thenOps = new ArrayList<>(ops.size());
		final List<Expr<?>> elseOps = new ArrayList<>(ops.size());

		for (final Expr<?> op : ops) {
			if (op == ite) {
				thenOps.add(ite.getThen());
				elseOps.add(ite.getElse());
			} else {
				thenOps.add(op);
				elseOps.add(op);
			}
		}

		return Ite(ite.getCond(), pushIte(expr.withOps(thenOps)), pushIte(expr.withOps(elseOps)));
	}

}
