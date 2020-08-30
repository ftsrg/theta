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
package hu.bme.mit.theta.solver;

import java.util.Collection;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

/**
 * Common interface for SMT solvers.
 *
 * Use the {@link #add(Expr)} methods to add expressions to the solver.
 * Then use {@link #check()} method to check their satisfiability. The result can be queried by
 * {@link #getStatus()}. If the expressions are satisfiable, a satisfying assignment can be
 * obtained by {@link #getModel()}.
 *
 * The solver can also support incremental solving by {@link #push()} and {@link #pop()}.
 */
public interface Solver {

	/**
	 * Add an expression to the solver.
	 *
	 * @param assertion Expression to be added
	 */
	void add(Expr<BoolType> assertion);

	/**
	 * Add a collection of expressions to the solver.
	 *
	 * @param assertions Expressions to be added
	 */
	default void add(final Iterable<? extends Expr<BoolType>> assertions) {
		for (final Expr<BoolType> assertion : assertions) {
			add(assertion);
		}
	}

	/**
	 * Check if the currently added expressions are satisfiable.
	 *
	 * @return Status
	 */
	SolverStatus check();

	/**
	 * Push the current solver state. When calling {@link #pop()}, all expressions added after
	 * the last push will be removed.
	 */
	void push();

	/**
	 * Remove expressions added after the previous n {@link #push()} calls.
	 *
	 * @param n
	 */
	void pop(final int n);

	/**
	 * Remove expressions added after the previous {@link #push()} call.
	 */
	default void pop() {
		pop(1);
	}

	/**
	 * Reset the solver state. It should be only used as a last resort. Try using
	 * {@link #push()} and {@link #pop()} instead. See also {@link hu.bme.mit.theta.solver.utils.WithPushPop}
	 * which implements try with resources pattern.
	 */
	void reset();

	/**
	 * Get the current status of the solver.
	 *
	 * @return Status
	 */
	SolverStatus getStatus();

	/**
	 * Get the satisfying assignment for the currently added expressions.
	 * Should only be called if {@link #check()} was already called and
	 * the result is SAT.
	 *
	 * @return Satisfying assignment
	 */
	Valuation getModel();

	/**
	 * Get the currently added expressions.
	 *
	 * @return Expressions
	 */
	Collection<Expr<BoolType>> getAssertions();
}
