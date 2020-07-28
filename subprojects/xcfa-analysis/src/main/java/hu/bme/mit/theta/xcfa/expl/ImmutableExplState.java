/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.expl;

import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Map;
import java.util.Objects;

/**
 * All the data needed for determining if two states are equal.
 * The point of this structure is to store only the minimum data.
 * (E.g. does not have enough data to execute a transition.)
 * TODO Currently does not support nested functions properly.
 */
public class ImmutableExplState extends AbstractExplState {

    private final ImmutableValuation valuation;
    private final ImmutableMap<XCFA.Process, ImmutableProcessState> locs;

    public ImmutableExplState(ImmutableValuation valuation, ImmutableMap<XCFA.Process, ImmutableProcessState> locs) {
        this.valuation = valuation;
        this.locs = locs;
    }

    @Override
    public Valuation getValuation() {
        return valuation;
    }

    @Override
    public Map<XCFA.Process, ImmutableProcessState> getLocations() {
        return locs;
    }

    @Override
    public int hashCode() {
        return Objects.hash(valuation, locs);
    }
}
