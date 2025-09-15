/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xsts.XSTS;

public class XstsPropInitPrec implements XstsInitPrec {

    @Override
    public ExplPrec createExpl(XSTS xsts) {
        return ExplPrec.of(ExprUtils.getVars(xsts.getProp()));
    }

    @Override
    public PredPrec createPred(XSTS xsts) {
        return PredPrec.of(ExprUtils.getAtoms(xsts.getProp()));
    }

    @Override
    public Prod2Prec<ExplPrec, PredPrec> createProd2ExplPred(XSTS xsts) {
        return Prod2Prec.of(
                ExplPrec.of(xsts.getCtrlVars()), PredPrec.of(ExprUtils.getAtoms(xsts.getProp())));
    }
}
