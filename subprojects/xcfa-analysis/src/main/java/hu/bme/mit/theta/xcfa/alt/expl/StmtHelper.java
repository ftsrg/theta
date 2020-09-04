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

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.xcfa.SyntheticType;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;
import hu.bme.mit.theta.xcfa.type.SyntheticLitExpr;

import java.util.Optional;
import java.util.function.BiFunction;

final class StmtHelper {
    public static void atomicBegin(ExplStateMutatorInterface state, XCFA.Process process) {
        state.atomicBegin(process);
    }

    public static void atomicEnd(ExplStateMutatorInterface state, XCFA.Process process) {
        state.atomicEnd(process);
    }

    public static <DeclType extends Type> void assign(ExplStateMutatorInterface state, AssignStmt<DeclType> assignStmt) {
        state.putValue(assignStmt.getVarDecl(), state.eval(assignStmt.getExpr()));
    }

    public static <DeclType extends Type> void havoc(ExplStateMutatorInterface state, HavocStmt<DeclType> havocStmt) {
        state.putValue(havocStmt.getVarDecl(), Optional.empty());
    }

    public static void call(ExplStateMutatorInterface state, XCFA.Process process, CallStmt stmt) {
        state.call(process, stmt);
    }

    public static boolean assume(ExplStateReadOnlyInterface readOnlyState, AssumeStmt assumeStmt) {
        return ((BoolLitExpr)readOnlyState.eval(assumeStmt.getCond()).orElse(BoolLitExpr.of(true))).getValue();
    }

    public static Optional<TransitionExecutorInterface> executeLockOperation(VarDecl<SyntheticType> syncVar, ExplStateReadOnlyInterface readOnlyState,
                                                                             BiFunction<SyntheticLitExpr, XCFA.Process, Optional<SyntheticLitExpr>> operation) {
        var optValue = readOnlyState.eval(syncVar.getRef());
        Preconditions.checkState(optValue.isPresent());
        SyntheticLitExpr sync0 = (SyntheticLitExpr) optValue.get();
        var syncOpt = operation.apply(sync0, readOnlyState.getTransitionProcess());
        return syncOpt.map(
                sync -> state -> {
                    if (sync.isInvalid()) {
                        state.setUnsafe("Bad locking");
                    }
                    state.putValue(syncVar, Optional.of(sync));
                }
        );
    }
}
