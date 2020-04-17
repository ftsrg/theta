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

import java.util.Collection;
import java.util.Optional;

final class StmtTransition implements Transition {

    private final Stmt stmt;
    private final XCFA.Process process;

    StmtTransition(Stmt stmt, XCFA.Process process) {
        this.stmt = stmt;
        this.process = process;
    }

    @Override
    public Optional<TransitionExecutorInterface> enabled(ExplStateReadOnlyInterface state) {
        return stmt.accept(ExplTransitionVisitor.getInstance(), state);
    }

    @Override
    public Collection<VarDecl<? extends Type>> getWVars() {
        return StmtUtils.getVars(stmt);
    }

    @Override
    public Collection<VarDecl<? extends Type>> getRWVars() {
        return StmtUtils.getWrittenVars(stmt);
    }

    @Override
    public boolean isLocal() {
        return LocalityUtils.isLocal(StmtUtils.getVars(stmt));
    }

    @Override
    public XCFA.Process getProcess() {
        return process;
    }
}
