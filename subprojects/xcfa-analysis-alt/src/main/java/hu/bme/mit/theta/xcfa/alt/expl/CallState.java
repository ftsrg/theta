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

/**
 * Represents all the data of a given call.
 * Used by ProcessState to handle and store one procedure call data.
 */
abstract class CallState {

    private final XCFA.Process process;

    private final XCFA.Process.Procedure procedure;

    @Nullable
    private final VarDecl<? extends Type> callerResultVar;

    /**
     * The variable to write the value to when returning from the procedure.
     * We need this data only to continue execution from the given state.
     */
    @Nullable
    public final VarDecl<? extends Type> getCallerResultVar() {
        return callerResultVar;
    }

    /** The process the called procedure belongs to. */
    public final XCFA.Process getProcess() {
        return process;
    }

    /** The procedure the call belongs to. */
    public final XCFA.Process.Procedure getProcedure() {
        return procedure;
    }

    public abstract XCFA.Process.Procedure.Location getLocation();

    /** Set the current location. Might be unimplemented (by ImmutableCallState). */
    public abstract void updateLocation(XCFA.Process.Procedure.Location target);

    /** Returns whether the final location is reached. */
    public final boolean isFinal() {
        return getProcedure().getFinalLoc() == getLocation();
    }

    /** Returns whether the error location is reached. */
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
