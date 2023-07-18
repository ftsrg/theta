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
package hu.bme.mit.theta.grammar.dsl

import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.*
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.grammar.dsl.stmt.StatementWrapper
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized

@RunWith(Parameterized::class)
class StmtTest {

    @Parameterized.Parameter(0)
    lateinit var memory: Stmt

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
                arrayOf(Assign(x, Int(1)), "(assign x 1)",
                    mapOf(Pair(ExprTest.NamedSymbol("x"), x))),
                arrayOf(Assume(Eq(x.ref, Int(1))), "(assume (= x 1))",
                    mapOf(Pair(ExprTest.NamedSymbol("x"), x))),
                arrayOf(Havoc(x), "(havoc x)", mapOf(Pair(ExprTest.NamedSymbol("x"), x))),
            )
        }
    }

    @Test
    fun testSerialize() {
        Assert.assertEquals(serialized, memory.toString())
    }

    @Test
    fun testDeserialize() {
        if (decls.any { it.value is ParamDecl }) return
        val symbolTable = SymbolTable()
        decls.forEach { symbolTable.add(it.key) }
        val env = Env()
        decls.forEach { env.define(it.key, it.value) }
        val stmt = StatementWrapper(serialized, SimpleScope(symbolTable)).instantiate(env)
        Assert.assertEquals(memory, stmt)
    }

    @Test
    fun testRoundTrip() {
        if (decls.any { it.value is ParamDecl }) return
        val symbolTable = SymbolTable()
        decls.forEach { symbolTable.add(it.key) }
        val env = Env()
        decls.forEach { env.define(it.key, it.value) }
        val stmt = StatementWrapper(memory.toString(), SimpleScope(symbolTable)).instantiate(env)
        Assert.assertEquals(memory, stmt)
    }

    data class NamedSymbol(val _name: String) : Symbol {

        override fun getName(): String {
            return _name
        }

    }
}