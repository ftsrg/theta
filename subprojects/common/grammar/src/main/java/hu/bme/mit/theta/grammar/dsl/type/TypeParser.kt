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
package hu.bme.mit.theta.grammar.dsl.type

import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.functype.FuncExprs.Func
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.rattype.RatExprs
import hu.bme.mit.theta.grammar.ThrowingErrorListener
import hu.bme.mit.theta.grammar.dsl.gen.TypeBaseVisitor
import hu.bme.mit.theta.grammar.dsl.gen.TypeLexer
import hu.bme.mit.theta.grammar.dsl.gen.TypeParser
import hu.bme.mit.theta.grammar.dsl.gen.TypeParser.*
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

class TypeWrapper(content: String) {

    private val context: TypeContext

    init {
        val lexer = TypeLexer(CharStreams.fromString(content))
        lexer.addErrorListener(ThrowingErrorListener)
        val parser = TypeParser(CommonTokenStream(lexer))
        parser.errorHandler = BailErrorStrategy()
        this.context = parser.type()
    }

    fun instantiate(): Type {
        return TypeCreatorVisitor.INSTANCE.visit(context)
    }

    private class TypeCreatorVisitor private constructor() : TypeBaseVisitor<Type>() {

        override fun visitBoolType(ctx: BoolTypeContext): Type {
            return BoolExprs.Bool()
        }

        override fun visitIntType(ctx: IntTypeContext): Type {
            return IntExprs.Int()
        }

        override fun visitRatType(ctx: RatTypeContext): Type {
            return RatExprs.Rat()
        }

        override fun visitArrayType(ctx: ArrayTypeContext): Type {
            val indexType: Type = ctx.indexType.accept<Type>(this)
            val elemType: Type = ctx.elemType.accept<Type>(this)
            return ArrayExprs.Array(indexType, elemType)
        }

        override fun visitBvType(ctx: BvTypeContext): Type {
            val size: Int = ctx.size.getText().toInt()
            return BvExprs.BvType(size)
        }

        override fun visitFpType(ctx: TypeParser.FpTypeContext): Type {
            val expSize = ctx.exponent.text.toInt()
            val sigSize = ctx.significand.text.toInt()
            return FpType.of(expSize, sigSize)
        }

        override fun visitFuncType(ctx: FuncTypeContext?): Type {
            return Func(ctx!!.from.accept(this), ctx.to.accept(this))
        }

        companion object {

            val INSTANCE = TypeCreatorVisitor()
        }
    }
}