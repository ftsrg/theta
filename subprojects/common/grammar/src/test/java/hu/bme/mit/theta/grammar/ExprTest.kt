/*
 *  Copyright 2022 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.grammar

import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.common.Tuple3
import hu.bme.mit.theta.common.dsl.*
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv
import hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType
import hu.bme.mit.theta.core.type.fptype.FpExprs.FpType
import hu.bme.mit.theta.core.type.fptype.FpLitExpr
import hu.bme.mit.theta.core.type.functype.FuncExprs.Func
import hu.bme.mit.theta.core.type.functype.FuncLitExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.utils.ExprUtils.simplify
import hu.bme.mit.theta.grammar.expr.ExpressionWrapper
import hu.bme.mit.theta.grammar.type.TypeWrapper
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized

@RunWith(Parameterized::class)
class ExprTest {
    @Parameterized.Parameter(0)
    lateinit var memory: Expr<*>

    @Parameterized.Parameter(1)
    lateinit var serialized: String

    @Parameterized.Parameter(2)
    lateinit var decls: Map<Symbol, Decl<*>>

    companion object {
        @JvmStatic
        @Parameterized.Parameters
        fun data(): Collection<Array<Any>> {
            val x = Var("x", Int())
            return listOf(
                    arrayOf(True(), "true", emptyMap<Symbol, Decl<*>>()),
                    arrayOf(False(), "false", emptyMap<Symbol, Decl<*>>()),

                    arrayOf(Int(0), "0", emptyMap<Symbol, Decl<*>>()),
                    arrayOf(Int(10), "10", emptyMap<Symbol, Decl<*>>()),
                    arrayOf(Int(-1), "-1", emptyMap<Symbol, Decl<*>>()),

                    arrayOf(Rat(1, 2), "1%2", emptyMap<Symbol, Decl<*>>()),
                    arrayOf(Rat(-1, 2), "-1%2", emptyMap<Symbol, Decl<*>>()),
                    arrayOf(Rat(10, -21), "-10%21", emptyMap<Symbol, Decl<*>>()),

                    arrayOf(Bv(BooleanArray(4) { it % 2 == 0 }), "4'b1010", emptyMap<Symbol, Decl<*>>()),

                    arrayOf(FpLitExpr.of(true, Bv(BooleanArray(4) { it % 2 == 0 }), Bv(BooleanArray(6) { it % 2 == 0 })), "-4'b1010.6'b101010", emptyMap<Symbol, Decl<*>>()),
                    arrayOf(FpLitExpr.of(false, Bv(BooleanArray(4) { it % 2 == 0 }), Bv(BooleanArray(6) { it % 2 == 0 })), "+4'b1010.6'b101010", emptyMap<Symbol, Decl<*>>()),

                    arrayOf(ArrayLitExpr.of(listOf(), Int(2), ArrayType.of(Int(), Int())), "(array (default 2))", emptyMap<Symbol, Decl<*>>()),
                    arrayOf(ArrayLitExpr.of(listOf(Tuple2.of(Int(0), Int(1))), Int(2), ArrayType.of(Int(), Int())), "(array (0 1) (default 2))", emptyMap<Symbol, Decl<*>>()),
                    arrayOf(ArrayLitExpr.of(listOf(Tuple2.of(Int(0), Int(1)), Tuple2.of(Int(1), Int(2))), Int(3), ArrayType.of(Int(), Int())), "(array (0 1) (1 2) (default 3))", emptyMap<Symbol, Decl<*>>()),

                    arrayOf(RefExpr.of(x), "x", mapOf(Pair(NamedSymbol("x"), x)))
            )
        }
    }


    @Test
    fun testSerialize() {
        Assert.assertEquals(serialized, memory.toString())
    }

    @Test
    fun testDeserialize() {
        val symbolTable = SymbolTable()
        decls.forEach { symbolTable.add(it.key) }
        val env = Env()
        decls.forEach { env.define(it.key, it.value) }
        Assert.assertEquals(simplify(ExpressionWrapper(SimpleScope(symbolTable), serialized).instantiate(env)), simplify(memory))
    }

    @Test
    fun testRoundTrip() {
        val symbolTable = SymbolTable()
        decls.forEach { symbolTable.add(it.key) }
        val env = Env()
        decls.forEach { env.define(it.key, it.value) }
        Assert.assertEquals(simplify(ExpressionWrapper(SimpleScope(symbolTable), memory.toString()).instantiate(env)), simplify(memory))
    }

    class NamedSymbol(val _name: String) : Symbol {
        override fun getName(): String {
            return _name
        }

    }
}