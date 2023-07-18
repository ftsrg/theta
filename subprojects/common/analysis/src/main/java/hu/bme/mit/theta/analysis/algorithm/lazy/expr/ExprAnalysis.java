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
package hu.bme.mit.theta.analysis.algorithm.lazy.expr;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprOrd;
import hu.bme.mit.theta.analysis.expr.IndexedExprState;
import hu.bme.mit.theta.analysis.expr.IndexedExprTransFunc;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.solver.Solver;

import static com.google.common.base.Preconditions.checkNotNull;

public final class ExprAnalysis implements Analysis<IndexedExprState, ExprAction, UnitPrec> {

    private final PartialOrd<IndexedExprState> partialOrd;
    private final ExprInitFunc initFunc;
    private final IndexedExprTransFunc transFunc;

    private ExprAnalysis(final Valuation initialValuation, final Solver solver) {
        checkNotNull(initialValuation);
        checkNotNull(solver);
        this.partialOrd = ExprOrd.create(solver)::isLeq;
        this.initFunc = ExprInitFunc.create(initialValuation);
        this.transFunc = IndexedExprTransFunc.getInstance();
    }

    public static ExprAnalysis create(final Valuation initialValuation, final Solver solver) {
        return new ExprAnalysis(initialValuation, solver);
    }

    @Override
    public PartialOrd<IndexedExprState> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public InitFunc<IndexedExprState, UnitPrec> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<IndexedExprState, ExprAction, UnitPrec> getTransFunc() {
        return transFunc;
    }
}
