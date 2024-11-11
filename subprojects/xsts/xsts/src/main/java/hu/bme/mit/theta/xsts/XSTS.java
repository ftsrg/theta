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
package hu.bme.mit.theta.xsts;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import java.util.Set;

public final class XSTS {

    private final Set<VarDecl<?>> vars;
    private final Set<VarDecl<?>> stateVars;
    private final Set<VarDecl<?>> localVars;
    private final Set<VarDecl<?>> ctrlVars;

    private final NonDetStmt tran;
    private final NonDetStmt env;
    private final NonDetStmt init;

    private final Expr<BoolType> initFormula;
    private final Expr<BoolType> prop;

    public NonDetStmt getTran() {
        return tran;
    }

    public NonDetStmt getEnv() {
        return env;
    }

    public NonDetStmt getInit() {
        return init;
    }

    public Expr<BoolType> getInitFormula() {
        return initFormula;
    }

    public Expr<BoolType> getProp() {
        return prop;
    }

    public Set<VarDecl<?>> getVars() {
        return vars;
    }

    public Set<VarDecl<?>> getLocalVars() {
        return localVars;
    }

    public Set<VarDecl<?>> getStateVars() {
        return stateVars;
    }

    public Set<VarDecl<?>> getCtrlVars() {
        return ctrlVars;
    }

    public XSTS(
            final Set<VarDecl<?>> ctrlVars,
            final NonDetStmt init,
            final NonDetStmt tran,
            final NonDetStmt env,
            final Expr<BoolType> initFormula,
            final Expr<BoolType> prop) {
        this.tran = checkNotNull(tran);
        this.init = checkNotNull(init);
        this.env = checkNotNull(env);
        this.initFormula = checkNotNull(initFormula);
        this.prop = checkNotNull(prop);
        this.ctrlVars = checkNotNull(ctrlVars);

        this.vars = Containers.createSet();
        vars.addAll(StmtUtils.getVars(tran));
        vars.addAll(StmtUtils.getVars(env));
        vars.addAll(StmtUtils.getVars(init));
        vars.addAll(ExprUtils.getVars(initFormula));
        vars.addAll(ExprUtils.getVars(prop));
        this.stateVars = this.vars;
        this.localVars = Containers.createSet();
    }

    public XSTS(
            final Set<VarDecl<?>> stateVars,
            final Set<VarDecl<?>> localVars,
            final Set<VarDecl<?>> ctrlVars,
            final NonDetStmt init,
            final NonDetStmt tran,
            final NonDetStmt env,
            final Expr<BoolType> initFormula,
            final Expr<BoolType> prop) {
        this.tran = checkNotNull(tran);
        this.init = checkNotNull(init);
        this.env = checkNotNull(env);
        this.initFormula = checkNotNull(initFormula);
        this.prop = checkNotNull(prop);
        this.ctrlVars = checkNotNull(ctrlVars);

        this.vars = Containers.createSet();
        this.vars.addAll(checkNotNull(stateVars));
        this.vars.addAll(checkNotNull(localVars));
        this.stateVars = stateVars;
        this.localVars = localVars;
    }
}
