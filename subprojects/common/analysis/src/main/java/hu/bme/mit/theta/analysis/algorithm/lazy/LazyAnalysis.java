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
package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public final class LazyAnalysis<SConcr extends State, SAbstr extends ExprState, A extends Action, P extends Prec> implements Analysis<LazyState<SConcr, SAbstr>, A, P> {

    private final LazyOrd<SConcr, SAbstr> partialOrd;
    private final LazyInitFunc<SConcr, SAbstr, P> initFunc;
    private final LazyTransFunc<SConcr, SAbstr, A, P> transFunc;

    private LazyAnalysis(final PartialOrd<SAbstr> abstrOrd,
                         final InitFunc<SConcr, P> concrInitFunc,
                         final TransFunc<SConcr, A, P> concrTransFunc,
                         final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        checkNotNull(abstrOrd);
        checkNotNull(concrInitFunc);
        checkNotNull(concrTransFunc);
        checkNotNull(initAbstractor);
        this.partialOrd = LazyOrd.create(abstrOrd);
        this.initFunc = LazyInitFunc.create(concrInitFunc, initAbstractor);
        this.transFunc = LazyTransFunc.create(concrTransFunc, initAbstractor);
    }

    public static <SConcr extends State, SAbstr extends ExprState, A extends Action, P extends Prec> LazyAnalysis<SConcr, SAbstr, A, P>
    create(final PartialOrd<SAbstr> abstrPartialOrd,
           final InitFunc<SConcr, P> concrInitFunc,
           final TransFunc<SConcr, A, P> concrTransFunc,
           final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        return new LazyAnalysis<>(abstrPartialOrd, concrInitFunc, concrTransFunc, initAbstractor);
    }

    @Override
    public PartialOrd<LazyState<SConcr, SAbstr>> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public InitFunc<LazyState<SConcr, SAbstr>, P> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<LazyState<SConcr, SAbstr>, A, P> getTransFunc() {
        return transFunc;
    }
}
