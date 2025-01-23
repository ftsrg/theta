/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.type.functype;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import java.util.List;

public final class FuncExprs {

    private FuncExprs() {}

    public static <ParamType extends Type, ResultType extends Type>
            FuncType<ParamType, ResultType> Func(
                    final ParamType paramType, final ResultType resultType) {
        return FuncType.of(paramType, resultType);
    }

    public static <ParamType extends Type, ResultType extends Type>
            FuncLitExpr<ParamType, ResultType> Func(
                    final ParamDecl<ParamType> paramDecl, final Expr<ResultType> result) {
        return FuncLitExpr.of(paramDecl, result);
    }

    public static <ParamType extends Type, ResultType extends Type>
            FuncAppExpr<ParamType, ResultType> App(
                    final Expr<FuncType<ParamType, ResultType>> func, final Expr<ParamType> param) {
        return FuncAppExpr.of(func, param);
    }

    private static <ParamType extends Type, ResultType extends Type>
            FuncAppExpr<ParamType, ResultType> App(
                    final Expr<FuncType<ParamType, ResultType>> func,
                    final Expr<ParamType> paramHead,
                    final List<Expr> paramTail) {
        if (!paramTail.isEmpty()) {
            final var newParamHead = paramTail.get(paramTail.size() - 1);
            final var newParamTail = paramTail.subList(0, paramTail.size() - 1);
            return App(App(func, newParamHead, newParamTail), paramHead);
        } else {
            return App(func, paramHead);
        }
    }

    public static <ParamType extends Type, ResultType extends Type>
            FuncAppExpr<ParamType, ResultType> App(
                    final Expr<FuncType<ParamType, ResultType>> func, final List<Expr> params) {
        checkArgument(!params.isEmpty());
        final var paramHead = params.get(params.size() - 1);
        final var paramTail = params.subList(0, params.size() - 1);
        return App(func, paramHead, paramTail);
    }

    public static <T1 extends Type, T2 extends Type> Expr<?> UnsafeApp(
            final Expr<?> func, final Expr<?> param) {
        checkState(
                func.getType() instanceof FuncType<?, ?> fFunc
                        && fFunc.getParamType().equals(param.getType()),
                "Parameter of type "
                        + param.getType()
                        + " is not suitable for function of type "
                        + func.getType());
        final Expr<FuncType<T1, T2>> funcTyped = (Expr<FuncType<T1, T2>>) func;
        final Expr<T1> paramTyped = (Expr<T1>) param;
        return App(funcTyped, paramTyped);
    }

    public static <T1 extends Type, T2 extends Type> Expr<?> UnsafeApp(
            final Expr<?> func, final List<Expr<?>> param) {
        checkState(
                func.getType() instanceof FuncType<?, ?> fFunc,
                "Supposed function is of type " + func.getType());
        final Expr<FuncType<T1, T2>> funcTyped = (Expr<FuncType<T1, T2>>) func;
        return App(funcTyped, param.stream().map(it -> (Expr) it).toList());
    }
}
