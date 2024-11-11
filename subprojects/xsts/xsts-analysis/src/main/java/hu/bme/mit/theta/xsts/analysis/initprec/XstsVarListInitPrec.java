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
package hu.bme.mit.theta.xsts.analysis.initprec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xsts.XSTS;
import java.util.Set;

public class XstsVarListInitPrec implements XstsInitPrec {
    Set<VarDecl<?>> vars;
    boolean transitionCoverage = true;

    public XstsVarListInitPrec(Set<VarDecl<?>> vars) {
        this.vars = vars;
    }

    public XstsVarListInitPrec setTransitionCoverage(boolean transitionCoverage) {
        this.transitionCoverage = transitionCoverage;
        return this;
    }

    @Override
    public ExplPrec createExpl(XSTS xsts) {
        vars.addAll(xsts.getCtrlVars());
        if (transitionCoverage) {
            for (VarDecl<?> var : xsts.getVars()) {
                if (var.getName().startsWith("__id_")) {
                    vars.add(var);
                }
            }
        }
        return ExplPrec.of(vars);
    }

    @Override
    public PredPrec createPred(XSTS xsts) {
        throw new RuntimeException(
                "Predicate precision is not supported with variable list precision");
    }

    @Override
    public Prod2Prec<ExplPrec, PredPrec> createProd2ExplPred(XSTS xsts) {
        throw new RuntimeException(
                "Prod2ExplPred precision is not supported with variable list precision");
    }
}
