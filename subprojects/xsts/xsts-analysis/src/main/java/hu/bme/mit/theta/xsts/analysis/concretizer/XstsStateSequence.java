/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xsts.analysis.concretizer;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.common.LispStringBuilder;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.XstsState;

import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

public final class XstsStateSequence {

    private final ImmutableList<XstsState<ExplState>> states;
    private final XSTS xsts;

    private XstsStateSequence(final List<XstsState<ExplState>> states, final XSTS xsts) {
        checkNotNull(states);
        checkArgument(!states.isEmpty(), "A trace must contain at least one state.");

        this.states = ImmutableList.copyOf(states);
        this.xsts = xsts;
    }

    public static XstsStateSequence of(final List<XstsState<ExplState>> states, final XSTS xsts) {
        return new XstsStateSequence(states, xsts);
    }

    public List<XstsState<ExplState>> getStates() {
        return states;
    }

    public XstsState<ExplState> getState(int index) {
        checkElementIndex(index, states.size());
        return states.get(index);
    }

    @Override
    public int hashCode() {
        return 31 * states.hashCode();
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final XstsStateSequence that = (XstsStateSequence) obj;
            return this.states.equals(that.states);
        } else {
            return false;
        }
    }

    public int length() {
        return states.size() - 1;
    }

    @Override
    public String toString() {
        final LispStringBuilder sb = Utils.lispStringBuilder(getClass().getSimpleName()).body();
        for (int i = 0; i <= length(); i++) {
            XstsState<ExplState> state = states.get(i);
            sb.add(Utils.lispStringBuilder(XstsState.class.getSimpleName())
                    .add(state.isInitialized() ? "post_init" : "pre_init")
                    .add(state.lastActionWasEnv() ? "last_env" : "last_internal").body()
                    .add(state.getState().toString()));
        }
        return sb.toString();
    }

}
