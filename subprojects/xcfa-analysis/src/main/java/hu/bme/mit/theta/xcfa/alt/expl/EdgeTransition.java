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

import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * A transition wrapping an edge with a statement.
 */
public final class EdgeTransition implements Transition {
    private final Edge edge;
    private final Transition innerTransition;
    private final XCFA.Process process;

    public EdgeTransition(XCFA.Process process, Edge edge) {
        Preconditions.checkArgument(edge.getStmts().size() == 1, "Edge should contain only 1 stmt!");
        innerTransition = new StmtTransition(edge.getStmts().get(0), process);
        this.edge = edge;
        this.process = process;
    }

    /**
     * The transition is enabled only when the internal transition is enabled.
     * When executed, also updates the location of the state.
     */
    @Override
    public Optional<TransitionExecutorInterface> enabled(ExplState state0) {
        return innerTransition.enabled(state0).map(
                enabledTransition -> (
                        state -> {
                            // Order is important, when a call is made.
                            // Call changes the current active call, used by updateLocation.
                            state.updateLocation(process, edge.getTarget());
                            enabledTransition.executeInternal(state);
                        }
                )
        );
    }

    /** Fall through */
    @Override
    public Set<VarDecl<? extends Type>> getWVars() {
        return innerTransition.getWVars();
    }

    /** Fall through */
    @Override
    public Set<VarDecl<? extends Type>> getRWVars() {
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

    public Transition getInnerTransition() {
        return innerTransition;
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder("Transition").add(edge).toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        EdgeTransition that = (EdgeTransition) o;
        return Objects.equals(edge, that.edge);
    }

    @Override
    public int hashCode() {
        return Objects.hash(edge);
    }
}
