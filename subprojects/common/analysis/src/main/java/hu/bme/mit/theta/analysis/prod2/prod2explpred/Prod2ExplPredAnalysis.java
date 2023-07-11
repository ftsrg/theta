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

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.*;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredAbstractors.Prod2ExplPredAbstractor;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredDedicatedTransFunc;

public final class Prod2ExplPredAnalysis<A extends ExprAction>
        implements Analysis<Prod2State<ExplState, PredState>, A, Prod2Prec<ExplPrec, PredPrec>> {

    private final PartialOrd<Prod2State<ExplState, PredState>> partialOrd;
    private final InitFunc<Prod2State<ExplState, PredState>, Prod2Prec<ExplPrec, PredPrec>> initFunc;
    private final TransFunc<Prod2State<ExplState, PredState>, A, Prod2Prec<ExplPrec, PredPrec>> transFunc;

    private Prod2ExplPredAnalysis(final Analysis<ExplState, ? super A, ExplPrec> analysis1,
                                  final Analysis<PredState, ? super A, PredPrec> analysis2,
                                  final StrengtheningOperator<ExplState, PredState, ExplPrec, PredPrec> strenghteningOperator,
                                  final Prod2ExplPredAbstractor prod2ExplPredAbstractor) {
        checkNotNull(analysis1);
        checkNotNull(analysis2);
        partialOrd = Prod2Ord.create(analysis1.getPartialOrd(), analysis2.getPartialOrd());
        initFunc = Prod2InitFunc.create(analysis1.getInitFunc(), analysis2.getInitFunc(),
                strenghteningOperator);
        transFunc = Prod2ExplPredDedicatedTransFunc.create(prod2ExplPredAbstractor);
    }

    public static <A extends ExprAction> Prod2ExplPredAnalysis<A> create(
            final Analysis<ExplState, ? super A, ExplPrec> analysis1,
            final Analysis<PredState, ? super A, PredPrec> analysis2,
            final StrengtheningOperator<ExplState, PredState, ExplPrec, PredPrec> strenghteningOperator,
            final Prod2ExplPredAbstractor prod2ExplPredAbstractor) {
        return new Prod2ExplPredAnalysis<A>(analysis1, analysis2, strenghteningOperator,
                prod2ExplPredAbstractor);
    }

    @Override
    public PartialOrd<Prod2State<ExplState, PredState>> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public InitFunc<Prod2State<ExplState, PredState>, Prod2Prec<ExplPrec, PredPrec>> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<Prod2State<ExplState, PredState>, A, Prod2Prec<ExplPrec, PredPrec>> getTransFunc() {
        return transFunc;
    }

}
