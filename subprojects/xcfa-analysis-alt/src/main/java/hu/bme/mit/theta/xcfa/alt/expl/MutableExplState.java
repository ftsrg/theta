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
package hu.bme.mit.theta.xcfa.alt.expl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.xcfa.SyntheticType;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

import javax.annotation.Nullable;
import java.util.Collection;
import java.util.Optional;
import java.util.stream.Collectors;

public final class MutableExplState extends ExplState implements ExplStateMutatorInterface {
    private final MutableValuation valuation;
    private final ProcessStates processStates;
    private VarIndexing indexing;
    private Safety internalSafety;
    private XCFA.Process atomicLock;

    /**
     * Checks that the time of checking if a transition is enabled is the same as the time of executing the transition
     * Must not be checked by equals or included in hashCode!
     */
    private int version=0;

    private MutableExplState(MutableValuation valuation, VarIndexing indexing, ProcessStates processStates, Safety internalSafety, XCFA.Process atomicLock) {
        this.valuation = valuation;
        this.indexing = indexing;
        this.processStates = processStates;
        this.internalSafety = internalSafety;
        this.atomicLock = atomicLock;
    }

    static MutableExplState initialState(XCFA xcfa) {
        return ExplState.initialState(xcfa, Factory.getInstance());
    }

    final void setUnsafe(String message) {
        internalSafety = Safety.unsafe(message);
    }

    public final Collection<ExecutableTransitionForMutableExplState> getEnabledTransitions() {
        return ExecutableTransitionUtils.getExecutableTransitions(this)
                .map(
                        x->new ExecutableTransitionForMutableExplState(MutableExplState.this, x, version)
                ).collect(Collectors.toUnmodifiableList());
    }

    public static MutableExplState copyOf(ExplState x) {
        return ExplState.copyOf(x, Factory.getInstance());
    }

    @Override
    public final MutableValuation getValuation() {
        return valuation;
    }

    @Override
    public final VarIndexing getIndexing() {
        return indexing;
    }

    @Override
    public final ProcessStates getProcessStates() {
        return processStates;
    }

    @Override
    public final Safety getInternalSafety() {
        return internalSafety;
    }

    @Override
    public final XCFA.Process getAtomicLock() {
        return atomicLock;
    }

    @Override
    public final void modifyIndexing(XCFA.Process.Procedure procedure, int modifier) {
        ValuesUtils.modifyIndexing(this, procedure, modifier);
    }

    @Override
    public void exitWait(VarDecl<SyntheticType> syncVar, XCFA.Process process) {
        ValuesUtils.executeLockOperation(this, syncVar, x->x.enterWait(process));
    }

    @Override
    public void enterWait(VarDecl<SyntheticType> syncVar, XCFA.Process process) {
        ValuesUtils.executeLockOperation(this, syncVar, x->x.exitWait(process));
    }

    @Override
    public void signalAll(VarDecl<SyntheticType> syncVar) {
        ValuesUtils.executeLockOperation(this, syncVar, x->x.signalAll());
    }

    @Override
    public final <DeclType extends Type> Optional<LitExpr<DeclType>> eval(Expr<DeclType> ref) {
        return ValuesUtils.eval(this, ref);
    }

    @Override
    public final void atomicBegin(XCFA.Process process) {
        AtomicUtils.begin(this, process);
    }

    @Override
    public final void atomicEnd(XCFA.Process process) {
        AtomicUtils.end(this, process);
    }

    @Override
    public final void lock(VarDecl<SyntheticType> syncVar, XCFA.Process process) {
        ValuesUtils.executeLockOperation(this, syncVar, x->x.lock(process));
    }

    @Override
    public final void unlock(VarDecl<SyntheticType> syncVar, XCFA.Process process) {
        ValuesUtils.executeLockOperation(this, syncVar, x->x.unlock(process));
    }

    @Override
    public final void call(XCFA.Process process, CallStmt stmt) {
        CallUtils.push(this, process, getProcess(process), stmt, Factory.getInstance());
    }

    @Override
    public final void leave(XCFA.Process process) {
        CallUtils.pop(getProcess(process), this);
    }

    @Override
    public final <DeclType extends Type> void putValue(VarDecl<DeclType> varDecl, Optional<LitExpr<DeclType>> declTypeLitExpr) {
        ValuesUtils.putValue(this, varDecl, declTypeLitExpr);
    }

    @Override
    public final void updateLocation(XCFA.Process process, XCFA.Process.Procedure.Location location) {
        getProcess(process).getActiveCallState().updateLocation(location);
    }

    final int getVersion() {
        return version;
    }

    final void changeVersion() {
        version++;
    }

    final void setAtomicLock(XCFA.Process process) {
        atomicLock = process;
    }

    void setIndexing(VarIndexing newIndexing) {
        indexing = newIndexing;
    }

    private static class Factory implements ExplState.Factory<MutableExplState> {

        private Factory() { }

        private static class LazyHolder {
            private static final Factory instance = new Factory();
        }

        static Factory getInstance() {
            return Factory.LazyHolder.instance;
        }

        @Override
        public MutableExplState create(Valuation valuation, VarIndexing indexing, ProcessStates states, Safety safety, XCFA.Process atomicLock) {
            return new MutableExplState(MutableValuation.copyOf(valuation), indexing, ProcessStates.copyOf(states, this), safety, atomicLock);
        }

        @Override
        public CallState createCallState(XCFA.Process process, XCFA.Process.Procedure procedure, XCFA.Process.Procedure.Location location, @Nullable VarDecl<? extends Type> callerResultVar) {
            return new MutableCallState(process, procedure, location, callerResultVar);
        }

    }

}
