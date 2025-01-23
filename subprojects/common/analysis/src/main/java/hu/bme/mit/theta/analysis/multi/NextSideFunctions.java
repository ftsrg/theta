/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.multi;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.unit.UnitState;

@SuppressWarnings("java:S119")
public final class NextSideFunctions {

    @FunctionalInterface
    public interface NextSideFunction<
            L extends State, R extends State, D extends State, MState extends MultiState<L, R, D>> {
        MultiSide defineNextSide(MState state);
    }

    public static class Alternating<
                    L extends State,
                    R extends State,
                    D extends State,
                    MState extends MultiState<L, R, D>>
            implements NextSideFunction<L, R, D, MState> {
        @Override
        public MultiSide defineNextSide(MState state) {
            return state.getSourceSide() == MultiSide.LEFT ? MultiSide.RIGHT : MultiSide.LEFT;
        }
    }

    public static class Alternating3<
                    L extends State,
                    RL extends State,
                    RR extends State,
                    D extends State,
                    MState extends MultiState<RL, RR, UnitState>,
                    MMState extends MultiState<L, MState, D>>
            implements NextSideFunction<L, MState, D, MMState> {
        @Override
        public MultiSide defineNextSide(MMState state) {
            return state.getSourceSide() == MultiSide.RIGHT
                            && state.getRightState().getSourceSide() == MultiSide.RIGHT
                    ? MultiSide.LEFT
                    : MultiSide.RIGHT;
        }
    }

    public static class Nondet<
                    L extends State,
                    R extends State,
                    D extends State,
                    MState extends MultiState<L, R, D>>
            implements NextSideFunction<L, R, D, MState> {
        @Override
        public MultiSide defineNextSide(MState state) {
            return MultiSide.BOTH;
        }
    }
}
