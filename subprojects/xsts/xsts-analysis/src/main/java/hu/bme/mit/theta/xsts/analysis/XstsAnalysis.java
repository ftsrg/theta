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
package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XstsAnalysis<S extends ExprState, P extends Prec>
        implements Analysis<XstsState<S>, XstsAction, P> {

    private final PartialOrd<XstsState<S>> partialOrd;
    private final InitFunc<XstsState<S>, P> initFunc;
    private final TransFunc<XstsState<S>, XstsAction, P> transFunc;

    private XstsAnalysis(final Analysis<S, ? super XstsAction, ? super P> analysis) {
        checkNotNull(analysis);
        partialOrd = XstsOrd.create(analysis.getPartialOrd());
        transFunc = XstsTransFunc.create(analysis.getTransFunc());
        initFunc = XstsInitFunc.create(analysis.getInitFunc());
    }

    public static <S extends ExprState, P extends Prec> XstsAnalysis<S, P> create(
            final Analysis<S, ? super XstsAction, ? super P> analysis) {
        return new XstsAnalysis<>(analysis);
    }

    @Override
    public PartialOrd<XstsState<S>> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public InitFunc<XstsState<S>, P> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<XstsState<S>, XstsAction, P> getTransFunc() {
        return transFunc;
    }
}
