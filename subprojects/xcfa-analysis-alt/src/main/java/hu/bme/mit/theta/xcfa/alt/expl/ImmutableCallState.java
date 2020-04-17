/*
 * Copyright 2019 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.alt.expl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;

import javax.annotation.Nullable;

final class ImmutableCallState extends CallState {

    private final XCFA.Process.Procedure.Location location;

    ImmutableCallState(XCFA.Process containingProcess, XCFA.Process.Procedure procedure, XCFA.Process.Procedure.Location location, @Nullable VarDecl<? extends Type> callerResultVar) {
        super(containingProcess, procedure, callerResultVar);
        this.location = location;
    }

    @Override
    public XCFA.Process.Procedure.Location getLocation() {
        return location;
    }

    @Override
    public void updateLocation(XCFA.Process.Procedure.Location target) {
        throw new UnsupportedOperationException("UpdateLocation called on immutable call state!");
    }

}
