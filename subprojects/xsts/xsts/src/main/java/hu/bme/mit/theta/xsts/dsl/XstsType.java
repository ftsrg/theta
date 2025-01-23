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
package hu.bme.mit.theta.xsts.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.dsl.ParseException;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslBaseVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.*;
import java.util.Optional;

final class XstsType {

    private final SymbolTable typeTable;
    private final TypeContext context;

    public XstsType(final SymbolTable typeTable, final TypeContext context) {
        this.typeTable = checkNotNull(typeTable);
        this.context = checkNotNull(context);
    }

    public Type instantiate(final Env env) {
        final TypeCreatorVisitor typeCreatorVisitor = new TypeCreatorVisitor(typeTable, env);
        final Type result = context.accept(typeCreatorVisitor);
        if (result == null) {
            throw new AssertionError();
        } else {
            return result;
        }
    }

    private static class TypeCreatorVisitor extends XstsDslBaseVisitor<Type> {

        private final SymbolTable typeTable;
        private final Env env;

        public TypeCreatorVisitor(final SymbolTable typeTable, final Env env) {
            this.typeTable = checkNotNull(typeTable);
            this.env = checkNotNull(env);
        }

        @Override
        public Type visitCustomType(final CustomTypeContext ctx) {
            Optional<? extends Symbol> optSymbol = typeTable.get(ctx.name.getText());
            if (optSymbol.isEmpty()) {
                throw new ParseException(
                        ctx, "Type '" + ctx.name.getText() + "' cannot be resolved");
            }
            final Symbol symbol = optSymbol.get();
            return (Type) env.eval(symbol);
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
        public Type visitArrayType(final ArrayTypeContext ctx) {
            final Type indexType = ctx.indexType.accept(this);
            final Type elemType = ctx.elemType.accept(this);
            return Array(indexType, elemType);
        }
    }
}
