/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.TypeUtils;

import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;

public final class FuncLitExpr<ParamType extends Type, ResultType extends Type>
        implements LitExpr<FuncType<ParamType, ResultType>> {

    private static final int HASH_SEED = 53;
    private static final String OPERATOR_LABEL = "func";

    private final ParamDecl<ParamType> param;
    private final Expr<ResultType> result;

    private volatile int hashCode = 0;

    private FuncLitExpr(final ParamDecl<ParamType> param, final Expr<ResultType> result) {
        this.param = checkNotNull(param);
        this.result = checkNotNull(result);
    }

    public static <ParamType extends Type, ResultType extends Type> FuncLitExpr<ParamType, ResultType> of(
            final ParamDecl<ParamType> param, final Expr<ResultType> result) {
        return new FuncLitExpr<>(param, result);
    }

    public ParamDecl<ParamType> getParam() {
        return param;
    }

    public Expr<ResultType> getResult() {
        return result;
    }

    @Override
    public FuncType<ParamType, ResultType> getType() {
        return Func(param.getType(), result.getType());
    }

    @Override
    public LitExpr<FuncType<ParamType, ResultType>> eval(final Valuation val) {
        return this;
    }

    @Override
    public int getArity() {
        return 1;
    }

    @Override
    public List<? extends Expr<?>> getOps() {
        return ImmutableList.of(result);
    }

    @Override
    public Expr<FuncType<ParamType, ResultType>> withOps(final List<? extends Expr<?>> ops) {
        checkNotNull(ops);
        checkArgument(ops.size() == 1);
        final Expr<ResultType> newResult = TypeUtils.cast(ops.get(0), result.getType());
        return with(newResult);
    }

    public FuncLitExpr<ParamType, ResultType> with(final Expr<ResultType> result) {
        if (this.result == result) {
            return this;
        } else {
            return FuncLitExpr.of(param, result);
        }
    }

    @Override
    public int hashCode() {
        int tmp = hashCode;
        if (tmp == 0) {
            tmp = HASH_SEED;
            tmp = 31 * tmp + param.hashCode();
            tmp = 31 * tmp + result.hashCode();
            hashCode = tmp;
        }
        return tmp;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final FuncLitExpr<?, ?> that = (FuncLitExpr<?, ?>) obj;
            return this.getParam().equals(that.getParam()) && this.getResult()
                    .equals(that.getResult());
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        final String paramString = String.format("(%s %s)", param.getName(), param.getType());
        return Utils.lispStringBuilder(OPERATOR_LABEL).body().add(paramString).add(result).toString();
    }

}
