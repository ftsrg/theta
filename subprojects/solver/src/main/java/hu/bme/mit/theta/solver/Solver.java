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
 * Use the {@link #add(Expr)} or {@link #track(Expr)} methods to add expressions to the solver.
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
	 * Add and track an expression. Required to calculate unsat cores.
	 * If you don't need unsat cores you can simply use {@link #add(Expr)}.
	 *
	 * @param assertion Expression to be tracked
	 */
	void track(Expr<BoolType> assertion);

	/**
	 * Add and track a collection of expressions.
	 *
	 * @param assertions Expressions to be tracked
	 */
	default void track(final Iterable<? extends Expr<BoolType>> assertions) {
		for (final Expr<BoolType> assertion : assertions) {
			track(assertion);
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
	 * Reset the solver state.
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
	 * Get an unsat core, i.e., a (not necessarily) minimal subset of the
	 * expressions that are already unsatisfiable. It only works if expressions
	 * were added by {@link #track(Expr)} or {@link #track(Iterable)} instead of
	 * {@link #add(Expr)} or {@link #add(Iterable)}. Furthermore, it should only
	 * be called if {@link #check()} was already called and the result is UNSAT.
	 *
	 * @return Unsat core
	 */
	Collection<Expr<BoolType>> getUnsatCore();

	/**
	 * Get the currently added expressions.
	 *
	 * @return Expressions
	 */
	Collection<Expr<BoolType>> getAssertions();
}
