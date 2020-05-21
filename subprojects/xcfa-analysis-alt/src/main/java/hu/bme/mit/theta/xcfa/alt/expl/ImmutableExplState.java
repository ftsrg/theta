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
package hu.bme.mit.theta.xcfa.alt.expl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xcfa.XCFA;

import javax.annotation.Nullable;
import java.util.Collection;
import java.util.stream.Collectors;

public final class ImmutableExplState extends ExplState {

    private final ImmutableValuation valuation;

    private final VarDoubleIndexing indexing;

    private final ProcessStates processStates;

    private final Safety internalSafety;

    private final XCFA.Process atomicLock;

    /**
     * A wrapper of ExecutableTransition for straight-forward usage in ImmutableExplState.
     * The execute() method should be used, which returns a new ImmutableExplState instance
     * with the transition executed.
     */
    public static final class ExecutableTransition extends ExecutableTransitionBase {
        private final ImmutableExplState immutableExplState;
        ExecutableTransition(ImmutableExplState immutableExplState, ExecutableTransitionBase transition) {
            super(transition, immutableExplState);
            this.immutableExplState = immutableExplState;
        }

        /**
         * @return Returns a new ImmutableExplState with the transition executed.
         */
        public final ImmutableExplState execute() {
            return new ImmutableExplState.Builder(immutableExplState).execute(this).build();
        }
    }

    public static ImmutableExplState copyOf(ExplState x) {
        if (x instanceof ImmutableExplState)
            return (ImmutableExplState) x;
        return ExplState.copyOf(x, Factory.getInstance());
    }

    private ImmutableExplState(ImmutableValuation valuation, VarDoubleIndexing indexing, ProcessStates states, Safety internalSafety,
                               XCFA.Process atomicLock) {
        this.valuation = valuation;
        this.indexing = indexing;
        this.processStates = states;
        this.internalSafety = internalSafety;
        this.atomicLock = atomicLock;
    }

    private static class Factory implements ExplState.Factory<ImmutableExplState> {

        @Override
        public ImmutableExplState create(
                Valuation valuation, VarDoubleIndexing indexing, ProcessStates states,
                Safety safety, XCFA.Process atomicLock
        ) {
            return new ImmutableExplState(ImmutableValuation.copyOf(valuation), indexing,
                    ProcessStates.copyOf(
                            states,
                            this
                    ), safety, atomicLock);
        }

        private static class LazyHolder {
            private static final Factory instance = new Factory();
        }

        public static Factory getInstance() {
            return LazyHolder.instance;
        }

        @Override
        public CallState createCallState(XCFA.Process process, XCFA.Process.Procedure procedure,
                                         XCFA.Process.Procedure.Location location, @Nullable VarDecl<? extends Type> callerResultVar) {
            return new ImmutableCallState(process, procedure, location, callerResultVar);
        }
    }

    public static ImmutableExplState initialState(XCFA xcfa) {
        return ExplState.initialState(xcfa, Factory.getInstance());
    }

    /**
     * Creates an executable transition with quick straight-forward usage
     * for immutable explicit state.
     */
    public ExecutableTransition transitionFrom(ExecutableTransitionBase transition) {
        return new ExecutableTransition(this, transition);
    }

    public Collection<ExecutableTransition> getEnabledTransitions() {
        return ExecutableTransitionUtils.getExecutableTransitions(this)
                .map(this::transitionFrom)
                .collect(Collectors.toUnmodifiableList());
    }

    @Override
    public Valuation getValuation() {
        return valuation;
    }

    @Override
    public VarDoubleIndexing getIndexing() {
        return indexing;
    }

    @Override
    public ProcessStates getProcessStates() {
        return processStates;
    }

    @Override
    public Safety getInternalSafety() {
        return internalSafety;
    }

    @Override
    public XCFA.Process getAtomicLock() {
        return atomicLock;
    }

    static final class Builder {
        final MutableExplState state;

        public Builder(ImmutableExplState state) {
            this.state = MutableExplState.copyOf(state);
        }

        Builder execute(TransitionExecutorInterface t) {
            t.executeInternal(state);
            return this;
        }

        public ImmutableExplState build() {
            return ImmutableExplState.copyOf(state);
        }
    }


}
