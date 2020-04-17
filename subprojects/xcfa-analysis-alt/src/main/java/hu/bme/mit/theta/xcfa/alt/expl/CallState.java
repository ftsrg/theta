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

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;

import javax.annotation.Nullable;
import java.util.Objects;

abstract class CallState {

    private final XCFA.Process process;

    private final XCFA.Process.Procedure procedure;

    @Nullable
    private final VarDecl<? extends Type> callerResultVar;

    /**
     * Determined by the last call. It is not a state of the call.
     * We need to remember this value to execute a statement.
     */
    @Nullable
    public final VarDecl<? extends Type> getCallerResultVar() {
        return callerResultVar;
    }

    public final XCFA.Process getProcess() {
        return process;
    }

    public final XCFA.Process.Procedure getProcedure() {
        return procedure;
    }

    public abstract XCFA.Process.Procedure.Location getLocation();

    public abstract void updateLocation(XCFA.Process.Procedure.Location target);

    public final boolean isFinal() {
        return getProcedure().getFinalLoc() == getLocation();
    }

    public final boolean isError() {
        return getProcedure().getErrorLoc() == getLocation();
    }

    protected CallState(XCFA.Process process, XCFA.Process.Procedure procedure, VarDecl<? extends Type> callerResultVar) {
        this.process = process;
        this.procedure = procedure;
        this.callerResultVar = callerResultVar;
    }

    public static CallState initial(XCFA.Process process, ExplState.Factory0 factory) {
        return factory.createCallState(process, process.getMainProcedure(), process.getMainProcedure().getInitLoc(), null);
    }

    @Override
    public final boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || !(o instanceof CallState)) return false;
        CallState that = (CallState) o;
        return getLocation().equals(that.getLocation());
    }

    @Override
    public final int hashCode() {
        return Objects.hash(getLocation());
    }

    @Override
    public final String toString() {
        return Utils.lispStringBuilder("CallState").add(getLocation()).toString();
    }
}
