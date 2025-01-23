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
package hu.bme.mit.theta.analysis.stubs;

import hu.bme.mit.theta.analysis.State;
import java.util.Objects;

public class StateStub implements State {

    private final String label;

    public StateStub(final String label) {
        this.label = label;
    }

    @Override
    public boolean isBottom() {
        return false;
    }

    @Override
    public String toString() {
        return label;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        StateStub stateStub = (StateStub) o;
        return Objects.equals(label, stateStub.label);
    }

    @Override
    public int hashCode() {
        return Objects.hash(label);
    }
}
