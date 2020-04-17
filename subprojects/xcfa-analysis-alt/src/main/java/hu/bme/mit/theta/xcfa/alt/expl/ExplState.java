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
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xcfa.XCFA;

import javax.annotation.Nullable;
import java.util.Objects;

public abstract class ExplState implements State {
    public abstract Valuation getValuation();
    public abstract VarIndexing getIndexing();
    public abstract ProcessStates getProcessStates();
    public abstract Safety getInternalSafety();
    public abstract XCFA.Process getAtomicLock();

    @Override
    public final int hashCode() {
        return Objects.hash(getValuation(), getProcessStates(), getIndexing(), getInternalSafety(), getAtomicLock());
    }

    private static boolean nullableEquals(Object a, Object b) {
        if (a == null && b == null)
            return true;
        if (a == null || b == null)
            return false;
        return a.equals(b);
    }

    interface Factory0 {
        CallState createCallState(XCFA.Process process, XCFA.Process.Procedure procedure,
                                  XCFA.Process.Procedure.Location location,
                                  @Nullable VarDecl<? extends Type> callerResultVar);
    }
    interface Factory<R> extends Factory0 {
        R create(
                Valuation valuation, VarIndexing indexing, ProcessStates states,
                Safety safety, XCFA.Process atomicLock
        );
    }

    protected static <R> R initialState(XCFA xcfa, Factory<R> factory) {
        LocalityUtils.init(xcfa);
        return factory.create(
                ValuesUtils.getInitialValuation(xcfa),
                ValuesUtils.getInitialIndexing(),
                ProcessStates.buildInitial(xcfa, factory),
                Safety.safe(),
                null);
    }

    protected static <R> R copyOf(ExplState x, Factory<R> factory) {
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
                getIndexing().equals(that.getIndexing()) &&
                nullableEquals(getAtomicLock(), that.getAtomicLock()) &&
                getInternalSafety().equals(that.getInternalSafety());
    }

    public final String toString() {
        return String.format("ImmutableExplStateImpl{valuation=%s\n indexing=%s\n processStates=%s\n internalSafety=%s\n atomicLock=%s\n}",
                getValuation(),
                getIndexing(),
                getProcessStates(),
                getInternalSafety(),
                getAtomicLock()
        );
    }

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
