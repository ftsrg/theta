/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xta.analysis.combinedlazycegar;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.xta.analysis.XtaAction;

public class CombinedLazyCegarXtaAnalysis<S extends State, P extends Prec>
        implements Analysis<S, XtaAction, P> {

    private final Analysis<S, ? super ExprAction, P> analysis;

    private final TransFunc<S, XtaAction, P> transFunc;

    private CombinedLazyCegarXtaAnalysis(final Analysis<S, ? super ExprAction, P> analysis) {
        this.analysis = analysis;
        this.transFunc = CombinedLazyCegarXtaTransFunc.create(analysis.getTransFunc());
    }

    public static <S extends State, P extends Prec> CombinedLazyCegarXtaAnalysis<S, P> create(
            final Analysis<S, ? super ExprAction, P> analysis) {
        return new CombinedLazyCegarXtaAnalysis<>(analysis);
    }

    @Override
    public PartialOrd<S> getPartialOrd() {
        return analysis.getPartialOrd();
    }

    @Override
    public InitFunc<S, P> getInitFunc() {
        return analysis.getInitFunc();
    }

    @Override
    public TransFunc<S, XtaAction, P> getTransFunc() {
        return transFunc;
    }
}
