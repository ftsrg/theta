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

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;

import javax.annotation.Nullable;
import java.util.Objects;

public abstract class ExplState implements State {
    /** Stores the values of the variables */
    public abstract Valuation getValuation();
    /** Stores the current depth of recursion for the procedure-local variables. */
    public abstract VarDoubleIndexing getIndexing();
    /** Stores the per-process states */
    public abstract ProcessStates getProcessStates();
    /** Stores whether special safety properties have been violated
     * (e.g. bad locking) */
    public abstract Safety getInternalSafety();
    /** On non-null, there is a pending atomic statement on the given process.
     * Only one process is enabled.
     */
    public abstract XCFA.Process getAtomicLock();

    @Override
    public final int hashCode() {
        return Objects.hash(getValuation(), getProcessStates(), getInternalSafety(), getAtomicLock());
    }

    private static boolean nullableEquals(Object a, Object b) {
        if (a == null && b == null)
            return true;
        if (a == null || b == null)
            return false;
        return a.equals(b);
    }

    /** These factories are used to reduce duplicated code in MutableExplState and ImmutableExplState.
     * CallState can be mutable or non-mutable, that's why we need to differentiate.
     */
    interface Factory0 {
        CallState createCallState(XCFA.Process process, XCFA.Process.Procedure procedure,
                                  XCFA.Process.Procedure.Location location,
                                  @Nullable VarDecl<? extends Type> callerResultVar);
    }
    /** These factories are used to reduce duplicated code in MutableExplState and ImmutableExplState. */
    interface Factory<R extends ExplState> extends Factory0 {
        R create(
                Valuation valuation, VarDoubleIndexing indexing, ProcessStates states,
                Safety safety, XCFA.Process atomicLock
        );
    }

    protected static <R extends ExplState> R initialState(XCFA xcfa, Factory<R> factory) {
        LocalityUtils.init(xcfa);
        return factory.create(
                ValuesUtils.getInitialValuation(xcfa),
                ValuesUtils.getInitialIndexing(),
                ProcessStates.buildInitial(xcfa, factory),
                Safety.safe(),
                null);
    }

    protected static <R extends ExplState> R copyOf(ExplState x, Factory<R> factory) {
        return factory.create(
                x.getValuation(),
                x.getIndexing(),
                x.getProcessStates(),
                x.getInternalSafety(),
                x.getAtomicLock()
        );
    }

    @Override
    public final boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || !(o instanceof ExplState)) return false;
        ExplState that = (ExplState) o;
        return getValuation().equals(that.getValuation()) &&
                getProcessStates().equals(that.getProcessStates()) &&
                nullableEquals(getAtomicLock(), that.getAtomicLock()) &&
                getInternalSafety().equals(that.getInternalSafety());
    }

    public final String toString() {
        return String.format("ImmutableExplStateImpl{valuation=%s%n indexing=%s%n processStates=%s%n internalSafety=%s%n atomicLock=%s%n}",
                getValuation(),
                getIndexing(),
                getProcessStates(),
                getInternalSafety(),
                getAtomicLock()
        );
    }

    /** Short-hand for usage of getProcessStates() */
    public final ProcessState getProcess(XCFA.Process process) {
        return getProcessStates().getStateOf(process);
    }

    public final Safety getSafety() {
        return SafetyUtils.getSafety(this);
    }

    @Override
    public final boolean isBottom() {
        return !getSafety().isSafe();
    }
}
