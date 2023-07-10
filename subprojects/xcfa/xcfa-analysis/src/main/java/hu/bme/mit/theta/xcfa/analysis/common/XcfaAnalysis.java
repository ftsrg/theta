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

package hu.bme.mit.theta.xcfa.analysis.common;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaAnalysis<S extends ExprState, A extends StmtAction, P extends Prec>
    implements Analysis<XcfaState<S>, A, XcfaPrec<P>> {

    private final PartialOrd<XcfaState<S>> partialOrd;
    private final InitFunc<XcfaState<S>, XcfaPrec<P>> initFunc;
    private final TransFunc<XcfaState<S>, A, XcfaPrec<P>> transFunc;

    private XcfaAnalysis(final List<XcfaLocation> initLoc, PartialOrd<XcfaState<S>> partialOrd,
        InitFunc<XcfaState<S>, XcfaPrec<P>> initFunc,
        TransFunc<XcfaState<S>, A, XcfaPrec<P>> transFunc) {
        this.partialOrd = partialOrd;
        this.initFunc = initFunc;
        this.transFunc = transFunc;
        checkNotNull(initLoc);
    }

    public static <S extends ExprState, A extends StmtAction, P extends Prec> XcfaAnalysis<S, A, P> create(
        final List<XcfaLocation> initLoc, PartialOrd<XcfaState<S>> partialOrd,
        InitFunc<XcfaState<S>, XcfaPrec<P>> initFunc,
        TransFunc<XcfaState<S>, A, XcfaPrec<P>> transFunc) {
        return new XcfaAnalysis<>(initLoc, partialOrd, initFunc, transFunc);
    }


    @Override
    public PartialOrd<XcfaState<S>> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public InitFunc<XcfaState<S>, XcfaPrec<P>> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<XcfaState<S>, A, XcfaPrec<P>> getTransFunc() {
        return transFunc;
    }
}
