/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Collection;

/**
 * Common interface for SMT solvers with unsat core capabilities.
 * <p>
 * Use the {@link #track(Expr)} method to add expressions to the solver. Then use {@link #check()}
 * method to check their satisfiability. The result can be queried by {@link #getStatus()}. If the
 * expressions are satisfiable, a satisfying assignment can be obtained by {@link #getModel()}. If
 * the expressions are not satisfiable, use {@link #getUnsatCore()} to obtain the unsat core.
 * <p>
 * The solver can also support incremental solving by {@link #push()} and {@link #pop()}.
 */
public interface UCSolver extends SolverBase {

    /**
     * Add and track an expression. Required to calculate unsat cores.
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
     * Get an unsat core, i.e., a (not necessarily) minimal subset of the expressions that are
     * already unsatisfiable. It only works if expressions were added by {@link #track(Expr)} or
     * {@link #track(Iterable)}. Furthermore, it should only be called if {@link #check()} was
     * already called and the result is UNSAT.
     *
     * @return Unsat core
     */
    Collection<Expr<BoolType>> getUnsatCore();
}
