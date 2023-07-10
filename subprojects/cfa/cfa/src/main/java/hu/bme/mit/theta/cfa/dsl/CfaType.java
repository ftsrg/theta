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
package hu.bme.mit.theta.cfa.dsl;

import hu.bme.mit.theta.cfa.dsl.gen.CfaDslBaseVisitor;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.fptype.FpType;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.ArrayTypeContext;
import static hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.BoolTypeContext;
import static hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.BvTypeContext;
import static hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.FpTypeContext;
import static hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.IntTypeContext;
import static hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.RatTypeContext;
import static hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.TypeContext;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

final class CfaType {

    private final TypeContext context;

    public CfaType(final TypeContext context) {
        this.context = checkNotNull(context);
    }

    public Type instantiate() {
        final Type result = TypeCreatorVisitor.INSTANCE.visit(context);
        if (result == null) {
            throw new AssertionError();
        } else {
            return result;
        }
    }

    private static class TypeCreatorVisitor extends CfaDslBaseVisitor<Type> {

        private static final TypeCreatorVisitor INSTANCE = new TypeCreatorVisitor();

        private TypeCreatorVisitor() {
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
        public Type visitArrayType(final ArrayTypeContext ctx) {
            final Type indexType = ctx.indexType.accept(this);
            final Type elemType = ctx.elemType.accept(this);
            return Array(indexType, elemType);
        }

        @Override
        public Type visitBvType(final BvTypeContext ctx) {
            final int size = Integer.parseInt(ctx.size.getText());
            return BvType(size);
        }

        @Override
        public Type visitFpType(FpTypeContext ctx) {
            final int expSize = getExp(ctx.getText());
            final int sigSize = getSignificand(ctx.getText());
            return FpType.of(expSize, sigSize);
        }

        private int getExp(String text) {
            Pattern pattern = Pattern.compile("\\[([0-9]*),([0-9]*)]");
            Matcher matcher = pattern.matcher(text);
            if (matcher.find()) {
                return Integer.parseInt(matcher.group(1));
            } else {
                throw new RuntimeException("Exponent not well formed in fp type!");
            }
        }

        private int getSignificand(String text) {
            Pattern pattern = Pattern.compile("\\[([0-9]*),([0-9]*)]");
            Matcher matcher = pattern.matcher(text);
            if (matcher.find()) {
                return Integer.parseInt(matcher.group(2));
            } else {
                throw new RuntimeException("Significand not well formed in fp type!");
            }
        }
    }

}
 
