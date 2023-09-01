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
package hu.bme.mit.theta.analysis.algorithm.bmc;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.common.LispStringBuilder;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;

import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory.indexing;

/**
 * Represents a mutable, alternating trace in the form of a (State, Action, State, ..., State,
 * Action, State) sequence. A trace always contains at least one state and the number of actions is
 * one less than the number of states.
 */
public final class BmcTrace<S extends ExprState, A extends StmtAction> {

    private final List<S> states;
    private final List<A> actions;
    private final List<Stmt> statements;

    private BmcTrace(final List<? extends S> states, final List<? extends A> actions,
                     final List<Stmt> statements) {
        checkNotNull(states);
        checkNotNull(actions);
        checkArgument(!states.isEmpty(), "A trace must contain at least one state.");
        checkArgument(states.size() == actions.size() + 1, "#states = #actions + 1 must hold.");
        this.states = new LinkedList<>(states);
        this.actions = new LinkedList<>(actions);
        this.statements = new LinkedList<>(statements);
    }

    private BmcTrace(final List<? extends S> states, final List<? extends A> actions) {
        this(states,
                actions,
                actions.stream().map(a -> a.getStmts().stream()).reduce(Streams::concat)
                        .map(s -> s.collect(Collectors.toList())).orElse(List.of()));
    }

    /**
     * Create a trace. The size of states must be at least one, and the size of the actions must be
     * one less than the number of states.
     */
    public static <S extends ExprState, A extends StmtAction> BmcTrace<S, A> of(
            final List<? extends S> states, final List<? extends A> actions) {
        return new BmcTrace<>(states, actions);
    }

    /**
     * Gets the length of the trace, which is the number of actions.
     */
    public int length() {
        return actions.size();
    }

    /**
     * Gets a state at a given index.
     *
     * @param i Index
     * @return State
     */
    public S getState(final int i) {
        checkElementIndex(0, states.size());
        return states.get(i);
    }

    /**
     * Gets an action at a given index
     *
     * @param i Index
     * @return Action
     */
    public A getAction(final int i) {
        checkElementIndex(0, actions.size());
        return actions.get(i);
    }

    /**
     * Gets all states.
     *
     * @return
     */
    public List<S> getStates() {
        return ImmutableList.copyOf(states);
    }

    /**
     * Gets all actions.
     *
     * @return
     */
    public List<A> getActions() {
        return ImmutableList.copyOf(actions);
    }

    /**
     * Creates a reversed trace by reversing both the states and the actions. The original trace is
     * not modified.
     *
     * @return Reversed trace
     */
    public BmcTrace<S, A> reverse() {
        return BmcTrace.of(Lists.reverse(states), Lists.reverse(actions));
    }

    public BmcTrace<S, A> copy() {
        return new BmcTrace<>(states, actions);
    }

    @Override
    public int hashCode() {
        return 31 * states.hashCode() + actions.hashCode();
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final BmcTrace<?, ?> that = (BmcTrace<?, ?>) obj;
            return this.states.equals(that.states) && this.actions.equals(that.actions);
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        final LispStringBuilder sb = Utils.lispStringBuilder(getClass().getSimpleName()).body();
        for (int i = 0; i < length(); i++) {
            sb.add(states.get(i));
            sb.add(actions.get(i));
        }
        sb.add(states.get(length()));
        return sb.toString();
    }

    public BmcTrace<S, A> addState(final S state, final A action) {
        states.add(state);
        actions.add(action);
        statements.addAll(action.getStmts());
        return this;
    }

    public S getLastState() {
        return states.get(states.size() - 1);
    }

    public boolean isFeasible(final Solver solver) {
        solver.push();
        StmtAction stmtAction = new StmtAction() {
            @Override
            public List<Stmt> getStmts() {
                return statements;
            }
        };
        solver.add(PathUtils.unfold(stmtAction.toExpr(), indexing(0)));
        if (solver.check().isUnsat()) {
            solver.pop();
            return false;
        }
        solver.pop();
        return true;
    }

    public Trace<S, A> toImmutableTrace() {
        return Trace.of(states, actions);
    }
}
