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
package hu.bme.mit.theta.core.dsl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static java.util.stream.Collectors.toList;

import hu.bme.mit.theta.core.dsl.gen.CoreDslBaseVisitor;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.ArrayTypeContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.BoolTypeContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.FuncTypeContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.IntTypeContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.RatTypeContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.TypeListContext;
import hu.bme.mit.theta.core.type.Type;
import java.util.Collections;
import java.util.List;

public final class TypeCreatorVisitor extends CoreDslBaseVisitor<Type> {

    private static final TypeCreatorVisitor INSTANCE = new TypeCreatorVisitor();

    private TypeCreatorVisitor() {}

    public static TypeCreatorVisitor getInstance() {
        return INSTANCE;
    }

    @Override
    public Type visitBoolType(final BoolTypeContext ctx) {
        return Bool();
    }

    @Override
    public Type visitIntType(final IntTypeContext ctx) {
        return Int();
    }

    @Override
    public Type visitRatType(final RatTypeContext ctx) {
        return Rat();
    }

    @Override
    public Type visitFuncType(final FuncTypeContext ctx) {
        final List<Type> paramTypes = createTypeList(ctx.paramTypes);

        checkArgument(paramTypes.size() == 1);
        final Type paramType = paramTypes.get(0);

        final Type resultType = ctx.returnType.accept(this);
        return Func(paramType, resultType);
    }

    @Override
    public Type visitArrayType(final ArrayTypeContext ctx) {
        final List<Type> indexTypes = createTypeList(ctx.indexTypes);

        checkArgument(indexTypes.size() == 1);
        final Type indexType = indexTypes.get(0);

        final Type elemType = ctx.elemType.accept(this);
        return Array(indexType, elemType);
    }

    private List<Type> createTypeList(final TypeListContext ctx) {
        if (ctx.types == null) {
            return Collections.emptyList();
        } else {
            final List<Type> types = ctx.types.stream().map(t -> t.accept(this)).collect(toList());
            return types;
        }
    }
}
