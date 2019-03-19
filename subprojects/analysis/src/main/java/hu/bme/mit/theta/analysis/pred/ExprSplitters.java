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
package hu.bme.mit.theta.analysis.pred;

import java.util.Collection;
import java.util.Collections;
import java.util.function.Function;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

/**
 * Strategies for splitting an expression into a collection of expressions.
 */
public final class ExprSplitters {

	/**
	 * Interface for splitting an expression into a collection of expressions.
	 */
	public interface ExprSplitter extends Function<Expr<BoolType>, Collection<Expr<BoolType>>> {
	}

	private ExprSplitters() {
	}

	/**
	 * Get the strategy that keeps the expression as a whole.
	 *
	 * @return
	 */
	public static ExprSplitter whole() {
		return new Whole();
	}

	/**
	 * Get the strategy that splits the expression into conjuncts.
	 *
	 * @return
	 */
	public static ExprSplitter conjuncts() {
		return new Conjuncts();
	}

	/**
	 * Get the strategy that splits the expression into atoms.
	 *
	 * @return
	 */
	public static ExprSplitter atoms() {
		return new Atoms();
	}

	private static final class Whole implements ExprSplitter {
		@Override
		public Collection<Expr<BoolType>> apply(final Expr<BoolType> expr) {
			return Collections.singleton(expr);
		}

		@Override
		public String toString() {
			return getClass().getSimpleName();
		}
	}

	private static final class Conjuncts implements ExprSplitter {
		@Override
		public Collection<Expr<BoolType>> apply(final Expr<BoolType> expr) {
			return ExprUtils.getConjuncts(expr);
		}

		@Override
		public String toString() {
			return getClass().getSimpleName();
		}
	}

	private static final class Atoms implements ExprSplitter {
		@Override
		public Collection<Expr<BoolType>> apply(final Expr<BoolType> expr) {
			return ExprUtils.getAtoms(expr);
		}

		@Override
		public String toString() {
			return getClass().getSimpleName();
		}
	}
}
