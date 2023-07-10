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
package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.PreStrengtheningOperator;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.ArrayList;

import static com.google.common.base.Preconditions.checkNotNull;

public final class Prod2ExplPredPreStrengtheningOperator implements
        PreStrengtheningOperator<ExplState, PredState> {

    private Prod2ExplPredPreStrengtheningOperator() {
    }

    public static Prod2ExplPredPreStrengtheningOperator create() {
        return new Prod2ExplPredPreStrengtheningOperator();
    }

    @Override
    public ExplState strengthenState1(Prod2State<ExplState, PredState> state) {
        checkNotNull(state);
        return state.getState1();
    }

    @Override
    public PredState strengthenState2(Prod2State<ExplState, PredState> state) {
        checkNotNull(state);
        var explState = state.getState1();
        var predState = state.getState2();

        var exprs = new ArrayList<Expr<BoolType>>();

        exprs.addAll(predState.getPreds());
        exprs.add(explState.getVal().toExpr());

        return PredState.of(exprs);
    }
}
