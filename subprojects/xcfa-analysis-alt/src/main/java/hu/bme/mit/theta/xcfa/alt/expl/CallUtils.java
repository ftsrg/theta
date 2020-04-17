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
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

final class CallUtils {

    public static void push(ExplStateMutatorInterface state, XCFA.Process process, ProcessState processState, CallStmt stmt, ExplState.Factory0 factory) {
        XCFA.Process.Procedure procedure = stmt.getProcedure();

        Preconditions.checkState(procedure.getParams().size() == stmt.getParams().size());
        // pass parameters...
        List<Optional<LitExpr<? extends Type>>> callerParameters = evalParams(state, stmt);

        processState.push(factory.createCallState(process, procedure, procedure.getInitLoc(), stmt.getResultVar()));
        state.modifyIndexing(procedure, 1);

        putParameterValues(state, procedure, callerParameters);
    }

    public static void pop(ProcessState processState, ExplStateMutatorInterface state) {
        XCFA.Process.Procedure oldProcedure = processState.getActiveCallState().getProcedure();
        VarDecl<? extends Type> whereToSaveResultUnindexed = processState.getActiveCallState().getCallerResultVar();

        Optional<LitExpr<? extends Type>> result = evalResult(state, oldProcedure);
        havocProcedureParametersAndVariables(state, oldProcedure);

        state.modifyIndexing(oldProcedure, -1);
        processState.pop();
        if (whereToSaveResultUnindexed != null && result.isPresent())
            state.putValue(whereToSaveResultUnindexed, (Optional)result);

    }

    private static List<Optional<LitExpr<? extends Type>>> evalParams(ExplStateMutatorInterface state, CallStmt callStmt) {
        List<Optional<LitExpr<? extends Type>>> callerParameters = new ArrayList<>();
        for (var x: callStmt.getParams()) {
            callerParameters.add(state.eval((Expr)x.getRef()));
        }
        return callerParameters;
    }

    private static void putParameterValues(ExplStateMutatorInterface state, XCFA.Process.Procedure procedure, List<Optional<LitExpr<? extends Type>>> z) {
        for (int i = 0; i < procedure.getParams().size(); i++) {
            state.putValue(procedure.getParams().get(i), z.get(i).map(x->(LitExpr)x));
        }
    }

    private static void havocProcedureParametersAndVariables(ExplStateMutatorInterface state, XCFA.Process.Procedure procedure) {
        procedure.getParams().forEach(x -> state.putValue(x, Optional.empty()));
        procedure.getLocalVars().forEach(x -> state.putValue(x, Optional.empty()));
    }

    private static Optional<LitExpr<? extends Type>> evalResult(ExplStateMutatorInterface state, XCFA.Process.Procedure procedure) {
        if (procedure.getResult() == null)
            return Optional.empty();
        return state.eval((Expr)procedure.getResult().getRef());
    }

}
