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

import java.util.Optional;

import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicBeginStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicEndStmt;
import hu.bme.mit.theta.core.stmt.xcfa.EnterWaitStmt;
import hu.bme.mit.theta.core.stmt.xcfa.ExitWaitStmt;
import hu.bme.mit.theta.core.stmt.xcfa.LoadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.MtxLockStmt;
import hu.bme.mit.theta.core.stmt.xcfa.MtxUnlockStmt;
import hu.bme.mit.theta.core.stmt.xcfa.NotifyAllStmt;
import hu.bme.mit.theta.core.stmt.xcfa.NotifyStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StoreStmt;
import hu.bme.mit.theta.core.stmt.xcfa.WaitStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaStmtVisitor;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;
import hu.bme.mit.theta.xcfa.type.SyntheticLitExpr;

/**
 * Creates an executor interface from a statement and a state.
 * The parameter (of type {@link ExplStateReadOnlyInterface}) must be only used to determine the enabledness
 * of the transition.
 * For modifying the state, the {@link TransitionExecutorInterface}'s parameter must be used!
 * The former one might be immutable (hence the name), or we do not want to have it mutated.
 * The latter, however is guaranteed to represent the exact same state (and maybe reference-equal).
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
        return Optional.of(state -> state.call(readOnlyState.getTransitionProcess(), (CallStmt)stmt));
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
        XCFA.Process process = readOnlyState.getTransitionProcess();
        return Optional.of(
                state -> StmtHelper.atomicBegin(state, process)
        );
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(AtomicEndStmt atomicEndStmt, ExplStateReadOnlyInterface readOnlyState) {
        XCFA.Process process = readOnlyState.getTransitionProcess();
        return Optional.of(
                state -> StmtHelper.atomicEnd(state, process)
        );
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(EnterWaitStmt stmt, ExplStateReadOnlyInterface readOnlyState) {
        return StmtHelper.executeLockOperation(stmt.getSyncVar(), readOnlyState, SyntheticLitExpr::enterWait);
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(ExitWaitStmt stmt, ExplStateReadOnlyInterface readOnlyState) {
        return StmtHelper.executeLockOperation(stmt.getSyncVar(), readOnlyState, SyntheticLitExpr::exitWait);
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(NotifyAllStmt notifyAllStmt, ExplStateReadOnlyInterface readOnlyState) {
        return StmtHelper.executeLockOperation(notifyAllStmt.getSyncVar(), readOnlyState, SyntheticLitExpr::signalAll);
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(NotifyStmt notifyStmt, ExplStateReadOnlyInterface readOnlyState) {
        throw new UnsupportedOperationException("Operation not supported!");
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(WaitStmt waitStmt, ExplStateReadOnlyInterface readOnlyState) {
        throw new UnsupportedOperationException("Operation not supported! Use DefaultTransformation to split wait into" +
                "two parts, needed here).");
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(MtxLockStmt lockStmt, ExplStateReadOnlyInterface readOnlyState) {
        return StmtHelper.executeLockOperation(lockStmt.getSyncVar(), readOnlyState, SyntheticLitExpr::lock);
    }

    @Override
    public Optional<TransitionExecutorInterface> visit(MtxUnlockStmt unlockStmt, ExplStateReadOnlyInterface readOnlyState) {
        return StmtHelper.executeLockOperation(unlockStmt.getSyncVar(), readOnlyState, SyntheticLitExpr::unlock);
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
