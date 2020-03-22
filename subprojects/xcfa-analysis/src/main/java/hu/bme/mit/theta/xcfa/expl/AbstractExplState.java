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

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Map;
import java.util.Objects;

/**
 * The triplet AbstractExplState-ExplState-ImmutableExplState is using the same idea as in
 * AbstractMap-HashMap-TreeMap: one "equals" method for two different implementations storing the same
 * data, without comparing the types themselves.
 */
public abstract class AbstractExplState implements State {
    public abstract Valuation getValuation();
    public abstract Map<XCFA.Process, ImmutableProcessState> getLocations();

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || !(o instanceof AbstractExplState)) return false;
        AbstractExplState that = (AbstractExplState) o;
        // comparing two maps (with different implementations) work, see AbsractMap's equals method:
        // https://docs.oracle.com/javase/7/docs/api/java/util/AbstractMap.html
        return getValuation().equals(that.getValuation()) &&
                getLocations().equals(that.getLocations());
    }


    @Override
    public String toString() {
        StringBuilder s = new StringBuilder();
        s.append(getValuation());
        s.append("\n");
        for (var x : getLocations().entrySet()) {
            s.append(Utils.lispStringBuilder().add(x.getKey()).add(x.getValue())).append("\n");
        }
        return s.toString();
    }

    @Override
    public int hashCode() {
        return Objects.hash(getValuation(), getLocations());
    }

    @Override
    public boolean isBottom() {
        return false;
    }
}
