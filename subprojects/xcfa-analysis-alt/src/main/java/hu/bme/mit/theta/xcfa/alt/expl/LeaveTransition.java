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

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Collection;
import java.util.Collections;
import java.util.Optional;

public final class LeaveTransition implements Transition {

    private final XCFA.Process process;
    private final CallState callState;

    public LeaveTransition(XCFA.Process process, CallState callState) {
        this.process = process;
        this.callState = callState;
    }
    @Override
    public Optional<TransitionExecutorInterface> enabled(ExplStateReadOnlyInterface state0) {
        return Optional.of(
                state -> state.leave(callState.getProcess())
        );
    }

    public Collection<VarDecl<? extends Type>> getWVars() {
        return Collections.singleton(callState.getCallerResultVar());
    }

    public Collection<VarDecl<? extends Type>> getRWVars() {
        // the procedure-local variable 'return' is read, but it is not a global, hence we do not need it
        return Collections.singleton(callState.getCallerResultVar());
    }

    @Override
    public XCFA.Process getProcess() {
        return process;
    }

    public boolean isLocal() {
        return LocalityUtils.isLocal(callState.getCallerResultVar());
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder("LeaveCall").add(callState.getProcedure()).toString();
    }
}
