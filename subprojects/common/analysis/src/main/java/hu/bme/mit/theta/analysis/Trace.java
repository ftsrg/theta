/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.LispStringBuilder;
import hu.bme.mit.theta.common.Utils;

import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Represents an immutable, alternating trace in the form of a (State, Action, State, ..., State,
 * Action, State) sequence. A trace always contains at least one state and the number of actions is
 * one less than the number of states.
 */
public final class Trace<S, A> implements Cex {

    private final ImmutableList<S> states;
    private final ImmutableList<A> actions;

    private Trace(final List<? extends S> states, final List<? extends A> actions) {
        checkNotNull(states);
        checkNotNull(actions);
        checkArgument(!states.isEmpty(), "A trace must contain at least one state.");
        checkArgument(states.size() == actions.size() + 1, "#states = #actions + 1 must hold.");
        this.states = ImmutableList.copyOf(states);
        this.actions = ImmutableList.copyOf(actions);
    }

    /**
     * Create a trace. The size of states must be at least one, and the size of the actions must be
     * one less than the number of states.
     */
    public static <S, A> Trace<S, A> of(final List<? extends S> states,
                                        final List<? extends A> actions) {
        return new Trace<>(states, actions);
    }

    /**
     * Gets the length of the trace, which is the number of actions.
     */
    @Override
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
        return states;
    }

    /**
     * Gets all actions.
     *
     * @return
     */
    public List<A> getActions() {
        return actions;
    }

    /**
     * Creates a reversed trace by reversing both the states and the actions. The original trace is
     * not modified.
     *
     * @return Reversed trace
     */
    public Trace<S, A> reverse() {
        return Trace.of(states.reverse(), actions.reverse());
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
            final Trace<?, ?> that = (Trace<?, ?>) obj;
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

}
