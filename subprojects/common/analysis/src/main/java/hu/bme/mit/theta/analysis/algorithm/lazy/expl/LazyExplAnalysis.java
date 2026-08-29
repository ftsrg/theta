/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.lazy.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.expl.ExplOrd;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.model.Valuation;

public class LazyExplAnalysis<A extends Action> implements Analysis<ExplState, A, UnitPrec> {
    private final LazyExplInitFunc initFunc;
    private final LazyExplTransFunc<A> transFunc;

    private LazyExplAnalysis(final Valuation initialValuation, final ExplPost<A> explPost) {
        checkNotNull(initialValuation);
        checkNotNull(explPost);
        initFunc = LazyExplInitFunc.create(initialValuation);
        transFunc = LazyExplTransFunc.create(explPost);
    }

    public static <A extends Action> LazyExplAnalysis<A> create(
            final Valuation initialValuation, final ExplPost<A> explPost) {
        return new LazyExplAnalysis<>(initialValuation, explPost);
    }

    @Override
    public PartialOrd<ExplState> getPartialOrd() {
        return ExplOrd.getInstance();
    }

    @Override
    public InitFunc<ExplState, UnitPrec> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<ExplState, A, UnitPrec> getTransFunc() {
        return transFunc;
    }
}
