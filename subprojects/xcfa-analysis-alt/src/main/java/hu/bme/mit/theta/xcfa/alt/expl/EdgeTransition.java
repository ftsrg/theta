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

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Edge;

import java.util.Collection;
import java.util.Optional;

final class EdgeTransition implements Transition {
    private final Edge edge;
    private final Transition innerTransition;
    private final XCFA.Process process;
    public EdgeTransition(XCFA.Process process, Edge edge) {
        Preconditions.checkArgument(edge.getStmts().size() == 1, "Edge should contain only 1 stmt!");
        innerTransition = new StmtTransition(edge.getStmts().get(0), process);
        this.edge = edge;
        this.process = process;
    }

    @Override
    public Optional<TransitionExecutorInterface> enabled(ExplStateReadOnlyInterface state0) {
        return innerTransition.enabled(state0).map(
                enabledTransition -> (
                        state -> {
                            state.updateLocation(process, edge.getTarget());
                            enabledTransition.executeInternal(state);
                        }
                )
        );
    }

    /** Fall through */
    @Override
    public Collection<VarDecl<? extends Type>> getWVars() {
        return innerTransition.getWVars();
    }

    /** Fall through */
    @Override
    public Collection<VarDecl<? extends Type>> getRWVars() {
        return innerTransition.getRWVars();
    }

    @Override
    public XCFA.Process getProcess() {
        return process;
    }

    /** Fall through */
    @Override
    public boolean isLocal() {
        return innerTransition.isLocal();
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder("EnabledTransition").add(edge).toString();
    }
}
