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
package hu.bme.mit.theta.xcfa.alt.transform;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaInternalNotifyStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaStmtVisitor;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.xcfa.SyntheticType;
import hu.bme.mit.theta.xcfa.XCFA;

/**
 * TODO find a subproject and a package where XCFA.Process is accessible, and the place is logical
 */
public class InternalNotifyStmt extends XcfaInternalNotifyStmt {
    private static final String STMT_LABEL = "enterwait";
    private final VarDecl<SyntheticType> syncVar;
    // not final to prevent circular dependency
    private XCFA.Process process;

    public InternalNotifyStmt(VarDecl<? extends Type> lhs, XCFA.Process process) {
        Preconditions.checkArgument(lhs.getType() == SyntheticType.getInstance(), STMT_LABEL + " stmt should be passed a synthetic");
        syncVar = (VarDecl<SyntheticType>) lhs;
        this.process = process;
    }

    @Override
    public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }

    @Override
    public <P, R> R accept(XcfaStmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }

    public VarDecl<SyntheticType> getSyncVar() {
        return syncVar;
    }

    public XCFA.Process getProcess() {
        return process;
    }

    public String toString() {
        return Utils.lispStringBuilder(STMT_LABEL).add(syncVar.getName()).toString();
    }

    public void setProcess(XCFA.Process process) {
        this.process = process;
    }
}
