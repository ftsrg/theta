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
package hu.bme.mit.theta.solver;

import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.List;
import java.util.Optional;

/**
 * A theory plugin that the solver calls back during search. Subclasses override the callbacks they
 * need and use the propagate methods to steer the search.
 *
 * <p>A propagator is attached to one solver by {@link
 * SolverFactory#createSolverWithPropagators(UserPropagator...)}, which binds it to that solver's
 * {@link Backend}. Only expressions passed to {@link #registerExpression} are reported to the
 * callbacks, and only those may appear in a conflict or as the premises of a consequence.
 */
public abstract class UserPropagator {

    /** The solver-side operations a backend provides to a bound propagator. */
    public interface Backend {
        void registerExpression(Expr<BoolType> expr);

        void propagateConflict(List<Expr<BoolType>> exprs);

        void propagateConsequence(List<Expr<BoolType>> exprs, Expr<BoolType> consequence);

        boolean propagateNextDecision(Expr<BoolType> expr, Optional<Boolean> value);
    }

    private Backend backend;

    /** Called by a solver backend when the propagator is attached; a propagator binds once. */
    public final void bind(final Backend backend) {
        checkState(this.backend == null, "The propagator is already bound to a solver");
        this.backend = backend;
    }

    private Backend backend() {
        checkState(backend != null, "The propagator is not bound to a solver");
        return backend;
    }

    /** A registered expression was assigned a value. */
    public void onKnownValue(final Expr<BoolType> expr, final boolean value) {}

    /** The solver branches on a registered expression. */
    public void onDecision(final Expr<BoolType> expr, final boolean value) {}

    /** The solver found a full assignment; propagating a conflict here rejects it. */
    public void onFinalCheck() {}

    public void onPush() {}

    public void onPop(final int levels) {}

    /** Reports the value of this expression to the callbacks. Does NOT add it to the solver. */
    public final void registerExpression(final Expr<BoolType> expr) {
        backend().registerExpression(expr);
    }

    /** The current values of these registered expressions cannot hold together. */
    public final void propagateConflict(final List<Expr<BoolType>> exprs) {
        backend().propagateConflict(exprs);
    }

    /** The current values of these registered expressions imply the consequence. */
    public final void propagateConsequence(
            final List<Expr<BoolType>> exprs, final Expr<BoolType> consequence) {
        backend().propagateConsequence(exprs, consequence);
    }

    /** Asks the solver to branch on this expression next, optionally with the given value. */
    public final boolean propagateNextDecision(
            final Expr<BoolType> expr, final Optional<Boolean> value) {
        return backend().propagateNextDecision(expr, value);
    }
}
