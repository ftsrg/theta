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

import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.stmt.xcfa.*;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

import java.util.Optional;

/**
 * ExplStateMutatorInterface parameter must be only used to determine the enabledness.
 * For modifying the state, the enabledTransition's parameter must be used!
 * This is because readOnlyState can be an ImmutableExplStateMutatorInterface, and when executing the state,
 * a MutableExplStateMutatorInterface is created that is passed as a parameter to the EnabledTransition::execute method.
 */
final class ExplTransitionVisitor implements XcfaStmtVisitor<ExplStateReadOnlyInterface, Optional<TransitionExecutorInterface>> {

    private static class LazyHolder {
        private static final ExplTransitionVisitor instance = new ExplTransitionVisitor();
    }

    public static ExplTransitionVisitor getInstance() {
        return LazyHolder.instance;
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(XcfaCallStmt stmt, ExplStateReadOnlyInterface readOnlyState) {
        return Optional.of(state -> state.call(readOnlyState.getProcess(), (CallStmt)stmt));
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(StoreStmt storeStmt, ExplStateReadOnlyInterface readOnlyState) {
        throw new UnsupportedOperationException("Operation not supported!");
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(LoadStmt loadStmt, ExplStateReadOnlyInterface readOnlyState) {
        throw new UnsupportedOperationException("Operation not supported!");
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(AtomicBeginStmt atomicBeginStmt, ExplStateReadOnlyInterface readOnlyState) {
        return Optional.of(
                state -> StmtHelper.atomicBegin(state, readOnlyState.getProcess())
        );
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(AtomicEndStmt atomicEndStmt, ExplStateReadOnlyInterface readOnlyState) {
        return Optional.of(
                state -> StmtHelper.atomicEnd(state, readOnlyState.getProcess())
        );
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(NotifyAllStmt notifyAllStmt, ExplStateReadOnlyInterface readOnlyState) {
        throw new UnsupportedOperationException("Operation not supported!");
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(NotifyStmt notifyStmt, ExplStateReadOnlyInterface readOnlyState) {
        throw new UnsupportedOperationException("Operation not supported!");
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(WaitStmt waitStmt, ExplStateReadOnlyInterface readOnlyState) {
        throw new UnsupportedOperationException("Operation not supported!");
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(LockStmt lockStmt, ExplStateReadOnlyInterface readOnlyState) {
        if (ValuesUtils.lockable(readOnlyState.eval(lockStmt.getSyncVar().getRef()), readOnlyState.getProcess()))
            return Optional.of(state -> StmtHelper.lock(state, readOnlyState.getProcess(), lockStmt));
        return Optional.empty();
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(UnlockStmt unlockStmt, ExplStateReadOnlyInterface readOnlyState) {
        return Optional.of(state -> StmtHelper.unlock(state, readOnlyState.getProcess(), unlockStmt));
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(SkipStmt stmt, ExplStateReadOnlyInterface readOnlyState) {
        return Optional.of(state -> {});
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(AssumeStmt stmt, ExplStateReadOnlyInterface readOnlyState) {
        if (StmtHelper.assume(readOnlyState, stmt)) {
            return Optional.of(state -> {});
        } else {
            return Optional.empty();
        }
    }

    @Override
    public <DeclType extends Type> Optional<TransitionExecutorInterface> visit(AssignStmt<DeclType> stmt, ExplStateReadOnlyInterface readOnlyState) {
        return Optional.of(state -> StmtHelper.assign(state, stmt));
    }

    @Override
    public <DeclType extends Type> Optional<TransitionExecutorInterface> visit(HavocStmt<DeclType> stmt, ExplStateReadOnlyInterface readOnlyState) {
        return Optional.of(state -> StmtHelper.havoc(state, stmt));
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(XcfaStmt xcfaStmt, ExplStateReadOnlyInterface readOnlyState) {
        return xcfaStmt.accept(this, readOnlyState);
    }
}
