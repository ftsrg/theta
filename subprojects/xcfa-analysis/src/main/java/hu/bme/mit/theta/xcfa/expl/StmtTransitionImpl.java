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
package hu.bme.mit.theta.xcfa.expl;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Collection;

public class StmtTransitionImpl extends StmtTransition{
    private final ProcedureData.EdgeWrapper edge;

    public StmtTransitionImpl(XCFA.Process p, ProcedureData.EdgeWrapper edge) {
        super(p);
        this.edge = edge;
    }

    @Override
    public void execute(ExplState state) {
        // Multiple statements on the same edge is not supported, because:
        // some special stmt could mess up everything with multiple statements:
        // L0 -> L1 {
        //   call proc()
        //   a = a + 2
        // }
        // this code would try to call proc(), then increment a by 2, and *only then* proceed to the call itself.

        // also, enabledness is hard to determine

        // Because of this, currently only one stmt per edge is enforced:

        CallState callState = state.getProcessState(getProcess()).getCallStackPeek();
        edge.getStmt().accept(StateUpdateVisitor.getInstance(), callState);
        callState.updateLocation(edge.getTarget());
    }

    @Override
    public boolean enabled(ExplState state) {
        Stmt stmt = edge.getStmt();
        CallState callState = state.getProcessState(getProcess()).getCallStackPeek();
        return stmt.accept(EnabledStmtVisitor.getInstance(), callState);
    }

    // read vars that don't change
    public Collection<VarDecl<?>> getRWVars() {
        return StmtUtils.getVars(edge.getStmt());
    }

    // read vars that do change
    public Collection<VarDecl<?>> getWVars() {
        return StmtUtils.getWrittenVars(edge.getStmt());
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder().add(edge.getSource().xcfaLocation.toString()).add(edge.getStmt().toString()).toString();
    }

    public Stmt getStmt() {
        return edge.getStmt();
    }
}
