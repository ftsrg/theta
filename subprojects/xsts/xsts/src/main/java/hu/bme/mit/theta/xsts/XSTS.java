/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xsts.type.XstsType;

import java.util.*;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XSTS {

    private final Collection<VarDecl<?>> vars;
    private final Map<VarDecl<?>, XstsType<?>> varToType;
    private final Set<VarDecl<?>> ctrlVars;

    private final NonDetStmt tran;
    private final NonDetStmt env;
    private final NonDetStmt init;

    private final Expr<BoolType> initFormula;
    private final Expr<BoolType> prop;

    public NonDetStmt getInit() {
        return init;
    }

    public Collection<VarDecl<?>> getVars() {
        return vars;
    }

    public Map<VarDecl<?>, XstsType<?>> getVarToType() {
        return varToType;
    }

    public Expr<BoolType> getProp() {
        return prop;
    }

    public NonDetStmt getTran() {
        return tran;
    }

    public Expr<BoolType> getInitFormula() {
        return initFormula;
    }

    public NonDetStmt getEnv() {
        return env;
    }

    public Set<VarDecl<?>> getCtrlVars() {
        return ctrlVars;
    }

    public XSTS(final Map<VarDecl<?>, XstsType<?>> varToType, final Set<VarDecl<?>> ctrlVars,
                final NonDetStmt init, final NonDetStmt tran, final NonDetStmt env,
                final Expr<BoolType> initFormula, final Expr<BoolType> prop) {
        this.tran = checkNotNull(tran);
        this.init = checkNotNull(init);
        this.env = checkNotNull(env);
        this.initFormula = checkNotNull(initFormula);
        this.prop = checkNotNull(prop);
        this.varToType = varToType;
        this.ctrlVars = ctrlVars;

        final Set<VarDecl<?>> tmpVars = Containers.createSet();
        tmpVars.addAll(varToType.keySet());
        tmpVars.addAll(StmtUtils.getVars(tran));
        tmpVars.addAll(StmtUtils.getVars(env));
        tmpVars.addAll(StmtUtils.getVars(init));
        tmpVars.addAll(ExprUtils.getVars(initFormula));
        tmpVars.addAll(ExprUtils.getVars(prop));
        this.vars = Collections.unmodifiableCollection(tmpVars);
    }

}
