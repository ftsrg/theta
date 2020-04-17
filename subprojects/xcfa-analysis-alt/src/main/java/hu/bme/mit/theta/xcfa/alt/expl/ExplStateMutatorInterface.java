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
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.xcfa.SyntheticType;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

import java.util.Optional;

interface ExplStateMutatorInterface {

    void updateLocation(XCFA.Process process, XCFA.Process.Procedure.Location location);

    <DeclType extends Type>void putValue(VarDecl<DeclType> varDecl, Optional<LitExpr<DeclType>> litExpr);

    <DeclType extends Type> Optional<LitExpr<DeclType>> eval(Expr<DeclType> ref);

    void begin(XCFA.Process process);

    void end(XCFA.Process process);

    void call(XCFA.Process process, CallStmt stmt);

    void leave(XCFA.Process process);

    void lock(VarDecl<SyntheticType> syncVar, XCFA.Process process);

    void unlock(VarDecl<SyntheticType> syncVar, XCFA.Process process);

    void modifyIndexing(XCFA.Process.Procedure oldProcedure, int modifier);
}
