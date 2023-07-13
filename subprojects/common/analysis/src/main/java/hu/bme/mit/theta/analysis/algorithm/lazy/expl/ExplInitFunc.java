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
package hu.bme.mit.theta.analysis.algorithm.lazy.expl;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.model.Valuation;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Collections.singleton;

final class ExplInitFunc implements InitFunc<ExplState, UnitPrec> {

    private final Valuation initialValuation;

    private ExplInitFunc(final Valuation initialValuation) {
        this.initialValuation = checkNotNull(initialValuation);
    }

    public static ExplInitFunc create(final Valuation initialValuation) {
        return new ExplInitFunc(initialValuation);
    }

    @Override
    public Collection<ExplState> getInitStates(final UnitPrec prec) {
        checkNotNull(prec);
        final ExplState initState = ExplState.of(initialValuation);
        return singleton(initState);
    }

}