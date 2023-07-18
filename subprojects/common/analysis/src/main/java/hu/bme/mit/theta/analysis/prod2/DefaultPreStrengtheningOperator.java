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
package hu.bme.mit.theta.analysis.prod2;

import hu.bme.mit.theta.analysis.State;

import static com.google.common.base.Preconditions.checkNotNull;

public final class DefaultPreStrengtheningOperator<S1 extends State, S2 extends State> implements
        PreStrengtheningOperator<S1, S2> {

    private DefaultPreStrengtheningOperator() {
    }

    public static <S1 extends State, S2 extends State> PreStrengtheningOperator<S1, S2> create() {
        return new DefaultPreStrengtheningOperator<>();
    }

    @Override
    public S1 strengthenState1(Prod2State<S1, S2> state) {
        checkNotNull(state);
        return state.getState1();
    }

    @Override
    public S2 strengthenState2(Prod2State<S1, S2> state) {
        checkNotNull(state);
        return state.getState2();
    }
}
