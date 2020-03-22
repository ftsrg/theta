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

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Objects;

public class ImmutableProcessState {
    final XCFA.Process.Procedure.Location loc;
    public ImmutableProcessState(XCFA.Process.Procedure.Location loc) {
        this.loc = loc;
    }

    @Override
    public String toString() {
        if (loc == null)
            return Utils.lispStringBuilder().add("<null>").toString();
        return loc.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ImmutableProcessState that = (ImmutableProcessState) o;
        return Objects.equals(loc, that.loc);
    }

    @Override
    public int hashCode() {
        return Objects.hash(loc);
    }
}
