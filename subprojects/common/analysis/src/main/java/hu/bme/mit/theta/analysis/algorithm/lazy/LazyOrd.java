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

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public final class LazyOrd<SConcr extends State, SAbstr extends ExprState> implements PartialOrd<LazyState<SConcr, SAbstr>> {

    private final PartialOrd<SAbstr> ord;

    private LazyOrd(final PartialOrd<SAbstr> ord) {
        this.ord = checkNotNull(ord);
    }

    public static <SConcr extends State, SAbstr extends ExprState> LazyOrd<SConcr, SAbstr> create(final PartialOrd<SAbstr> ord) {
        return new LazyOrd<>(ord);
    }

    @Override
    public boolean isLeq(final LazyState<SConcr, SAbstr> state1, final LazyState<SConcr, SAbstr> state2) {
        return ord.isLeq(state1.getAbstrState(), state2.getAbstrState());
    }
}
