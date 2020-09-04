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
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Optional;
import java.util.Set;

public final class StmtTransition implements Transition {

    private final Stmt stmt;
    private final XCFA.Process process;

    StmtTransition(Stmt stmt, XCFA.Process process) {
        this.stmt = stmt;
        this.process = process;
    }

    @Override
    public Optional<TransitionExecutorInterface> enabled(ExplState state) {
        return stmt.accept(ExplTransitionVisitor.getInstance(),
                new ExplStateReadOnlyInterfaceImpl(getProcess(), state));
    }

    @Override
    public Set<VarDecl<? extends Type>> getWVars() {
        try {
            return StmtUtils.getWrittenVars(stmt);
        } catch (UnsupportedOperationException ex) {
            // if we cannot collect the variables, then turn off optimization
            return null;
        }
    }

    @Override
    public Set<VarDecl<? extends Type>> getRWVars() {
        try {
            return StmtUtils.getVars(stmt);
        } catch (UnsupportedOperationException ex) {
            // if we cannot collect the variables, then turn off optimization
            return null;
        }
    }

    @Override
    public boolean isLocal() {
        var vars = getRWVars();
        if (vars == null)
            return false;
        return LocalityUtils.isLocal(vars);
    }

    @Override
    public XCFA.Process getProcess() {
        return process;
    }

    public Stmt getStmt() {
        return stmt;
    }
}
