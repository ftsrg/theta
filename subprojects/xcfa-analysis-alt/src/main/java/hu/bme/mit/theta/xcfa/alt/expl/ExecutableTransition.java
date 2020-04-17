/*
 * Copyright 2019 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.alt.expl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Collection;
import java.util.Optional;

public class ExecutableTransition implements Transition, TransitionExecutorInterface {
    private final Transition transition;
    private final TransitionExecutorInterface executor;

    protected ExecutableTransition(ExecutableTransition et) {
        this.transition = et.transition;
        this.executor = et.executor;
    }

    private ExecutableTransition(Transition transition, TransitionExecutorInterface executor) {
        this.transition = transition;
        this.executor = executor;
    }

    static Optional<ExecutableTransition> from(ExplState state, Transition transition) {
        return transition.enabled(
                new ExplStateReadOnlyInterfaceImpl(transition.getProcess(), state)
        ).map(
                t->new ExecutableTransition(transition, t)
        );
    }

    @Override
    public Optional<TransitionExecutorInterface> enabled(ExplStateReadOnlyInterface state) {
        return Optional.of(executor);
    }

    @Override
    public Collection<VarDecl<? extends Type>> getWVars() {
        return transition.getWVars();
    }

    @Override
    public Collection<VarDecl<? extends Type>> getRWVars() {
        return transition.getRWVars();
    }

    @Override
    public XCFA.Process getProcess() {
        return transition.getProcess();
    }

    @Override
    public boolean isLocal() {
        return transition.isLocal();
    }

    @Override
    public void executeInternal(ExplStateMutatorInterface state) {
        executor.executeInternal(state);
    }

    @Override
    public String toString() {
        return transition.toString();
    }
}
