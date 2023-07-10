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
package hu.bme.mit.theta.analysis.expr.refinement.autoexpl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Set;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public class StaticAutoExpl implements AutoExpl {

    private final Set<VarDecl<?>> ctrlVars;

    public StaticAutoExpl(final Set<VarDecl<?>> ctrlVars) {
        this.ctrlVars = ctrlVars;
    }

    @Override
    public boolean isExpl(final VarDecl<?> decl) {
        return ctrlVars.contains(decl) || decl.getType() == Bool();
    }

    @Override
    public void update(final Expr<BoolType> itp) {
    }
}
