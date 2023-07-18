/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.smtlib.solver.transformer;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;

public interface SmtLibTermTransformer {

    <P extends Type, R extends Type> LitExpr<FuncType<P, R>> toFuncLitExpr(String funcLitImpl,
                                                                           FuncType<P, R> type, SmtLibModel model);

    <T extends Type> Expr<T> toExpr(String term, T type, SmtLibModel model);

    <T extends Type> LitExpr<T> toLitExpr(String litImpl, T type, SmtLibModel model);

    <I extends Type, E extends Type> LitExpr<ArrayType<I, E>> toArrayLitExpr(String arrayLitImpl,
                                                                             ArrayType<I, E> type, SmtLibModel model);

    LitExpr<BvType> toBvLitExpr(String bvLitImpl, BvType type, SmtLibModel model);
}
