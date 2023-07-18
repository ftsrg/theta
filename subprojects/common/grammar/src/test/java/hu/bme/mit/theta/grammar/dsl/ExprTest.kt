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

import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.bvtype.BvExprs.*
import hu.bme.mit.theta.core.type.fptype.FpExprs
import hu.bme.mit.theta.core.type.fptype.FpExprs.Max
import hu.bme.mit.theta.core.type.fptype.FpExprs.Min
import hu.bme.mit.theta.core.type.fptype.FpLitExpr
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.utils.ExprUtils.simplify
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper
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
            val p = Param("p", Int())

            val bvLit1 = Bv(BooleanArray(4) { it % 2 == 0 })
            val bvLit2 = Bv(BooleanArray(4) { it % 2 == 1 })
            val fpLit1 = FpLitExpr.of(true, bvLit1, Bv(BooleanArray(6) { it % 2 == 0 }))
            val fpLit2 = FpLitExpr.of(false, bvLit1, Bv(BooleanArray(6) { it % 2 == 0 }))

            return listOf(
                arrayOf(True(), "true", emptyMap<Symbol, Decl<*>>()),
                arrayOf(False(), "false", emptyMap<Symbol, Decl<*>>()),

                arrayOf(Int(0), "0", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Int(10), "10", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Int(-1), "-1", emptyMap<Symbol, Decl<*>>()),

                arrayOf(Rat(1, 2), "1%2", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Rat(-1, 2), "-1%2", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Rat(10, -21), "-10%21", emptyMap<Symbol, Decl<*>>()),

                arrayOf(bvLit1, "#b1010", emptyMap<Symbol, Decl<*>>()),

                arrayOf(fpLit1, "(#b1 #b1010 #b101010)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(fpLit2, "(#b0 #b1010 #b101010)", emptyMap<Symbol, Decl<*>>()),

                arrayOf(ArrayLitExpr.of(listOf(), Int(2), ArrayType.of(Int(), Int())),
                    "(array (default 2))", emptyMap<Symbol, Decl<*>>()),
                arrayOf(ArrayLitExpr.of(listOf(Tuple2.of(Int(0), Int(1))), Int(2),
                    ArrayType.of(Int(), Int())), "(array (0 1) (default 2))",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(
                    ArrayLitExpr.of(listOf(Tuple2.of(Int(0), Int(1)), Tuple2.of(Int(1), Int(2))),
                        Int(3), ArrayType.of(Int(), Int())), "(array (0 1) (1 2) (default 3))",
                    emptyMap<Symbol, Decl<*>>()),

                arrayOf(RefExpr.of(x), "x", mapOf(Pair(NamedSymbol("x"), x))),

                arrayOf(Ite<IntType>(True(), Int(1), Int(2)), "(ite true 1 2)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(Iff(True(), False()), "(iff true false)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Imply(True(), False()), "(=> true false)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Forall(listOf(p), True()), "(forall ((p Int)) true)",
                    mapOf(Pair(NamedSymbol("p"), p))),
                arrayOf(Exists(listOf(p), True()), "(exists ((p Int)) true)",
                    mapOf(Pair(NamedSymbol("p"), p))),

                arrayOf(Max(fpLit1, fpLit2), "(fpmax (#b1 #b1010 #b101010) (#b0 #b1010 #b101010))",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(Min(fpLit1, fpLit2), "(fpmin (#b1 #b1010 #b101010) (#b0 #b1010 #b101010))",
                    emptyMap<Symbol, Decl<*>>()),

                arrayOf(Or(True(), False()), "(or true false)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Xor(True(), False()), "(xor true false)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(And(True(), False(), False()), "(and true false false)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(Not(True()), "(not true)", emptyMap<Symbol, Decl<*>>()),

                arrayOf(Eq(Int(1), Int(2)), "(= 1 2)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Lt(Int(1), Int(2)), "(< 1 2)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Leq(Int(1), Int(2)), "(<= 1 2)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Gt(Int(1), Int(2)), "(> 1 2)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Geq(Int(1), Int(2)), "(>= 1 2)", emptyMap<Symbol, Decl<*>>()),

                arrayOf(BvExprs.ULt(bvLit1, bvLit1), "(bvult #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.ULeq(bvLit1, bvLit1), "(bvule #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.UGt(bvLit1, bvLit1), "(bvugt #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.UGeq(bvLit1, bvLit1), "(bvuge #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.SLt(bvLit1, bvLit1), "(bvslt #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.SLeq(bvLit1, bvLit1), "(bvsle #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.SGt(bvLit1, bvLit1), "(bvsgt #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.SGeq(bvLit1, bvLit1), "(bvsge #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.Or(listOf(bvLit1, bvLit1)), "(bvor #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.Xor(listOf(bvLit1, bvLit1)), "(bvxor #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.And(listOf(bvLit1, bvLit1)), "(bvand #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.ShiftLeft(bvLit1, bvLit1), "(bvshl #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.ArithShiftRight(bvLit1, bvLit1), "(bvashr #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.LogicShiftRight(bvLit1, bvLit1), "(bvlshr #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.RotateLeft(bvLit1, bvLit1), "(bvrol #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.RotateRight(bvLit1, bvLit1), "(bvror #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),

                arrayOf(Add(listOf(Int(1), Int(2), Int(3))), "(+ 1 2 3)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(Sub(Int(1), Int(2)), "(- 1 2)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Add(bvLit1, bvLit1), "(bvadd #b1010 #b1010)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Sub(bvLit1, bvLit1), "(bvsub #b1010 #b1010)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Add(fpLit1, fpLit2), "(fpadd (#b1 #b1010 #b101010) (#b0 #b1010 #b101010))",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(Sub(fpLit1, fpLit2), "(fpsub (#b1 #b1010 #b101010) (#b0 #b1010 #b101010))",
                    emptyMap<Symbol, Decl<*>>()),

                arrayOf(Mul(listOf(Int(1), Int(2), Int(3))), "(* 1 2 3)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(Div(Int(1), Int(2)), "(div 1 2)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Mod(Int(1), Int(2)), "(mod 1 2)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Rem(Int(1), Int(2)), "(rem 1 2)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Mul(bvLit1, bvLit1), "(bvmul #b1010 #b1010)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(UDiv(bvLit1, bvLit1), "(bvudiv #b1010 #b1010)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.SDiv(bvLit1, bvLit2), "(bvsdiv #b1010 #b0101)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.SMod(bvLit1, bvLit2), "(bvsmod #b1010 #b0101)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.URem(bvLit1, bvLit2), "(bvurem #b1010 #b0101)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(BvExprs.SRem(bvLit1, bvLit2), "(bvsrem #b1010 #b0101)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(Mul(fpLit1, fpLit2), "(fpmul (#b1 #b1010 #b101010) (#b0 #b1010 #b101010))",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(FpExprs.Div(FpRoundingMode.RNE, fpLit1, fpLit2),
                    "(fpdiv[rne] (#b1 #b1010 #b101010) (#b0 #b1010 #b101010))",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(FpExprs.Rem(fpLit1, fpLit2),
                    "(fprem (#b1 #b1010 #b101010) (#b0 #b1010 #b101010))",
                    emptyMap<Symbol, Decl<*>>()),

                arrayOf(Concat(listOf(bvLit1, bvLit2)), "(++ #b1010 #b0101)",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(ZExt(bvLit1, BvType(5)), "(bv_zero_extend #b1010 (Bv 5))",
                    emptyMap<Symbol, Decl<*>>()),
                arrayOf(SExt(bvLit1, BvType(5)), "(bv_sign_extend #b1010 (Bv 5))",
                    emptyMap<Symbol, Decl<*>>()),

                arrayOf(Pos(Int(1)), "(+ 1)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Neg(Int(1)), "(- 1)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Pos(bvLit1), "(bvpos #b1010)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Neg(bvLit1), "(bvneg #b1010)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Not(bvLit1), "(bvnot #b1010)", emptyMap<Symbol, Decl<*>>()),

                arrayOf(ArrayReadExpr.create<IntType, IntType>(
                    ArrayLitExpr.of(emptyList(), Int(2), ArrayType.of(Int(), Int())), Int(5)),
                    "(read (array (default 2)) 5)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(ArrayWriteExpr.create<IntType, IntType>(
                    ArrayLitExpr.of<IntType, IntType>(emptyList(), Int(2),
                        ArrayType.of(Int(), Int())), Int(5), Int(6)),
                    "(write (array (default 2)) 5 6)", emptyMap<Symbol, Decl<*>>()),

                arrayOf(Prime(Int(1)), "(prime 1)", emptyMap<Symbol, Decl<*>>()),
                arrayOf(Extract(bvLit1, Int(1), Int(4)), "(extract #b1010 1 4)",
                    emptyMap<Symbol, Decl<*>>()),

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
        val expr = simplify(
            ExpressionWrapper(SimpleScope(symbolTable), serialized).instantiate(env))
        Assert.assertEquals(simplify(memory), expr)
    }

    @Test
    fun testRoundTrip() {
        if (decls.any { it.value is ParamDecl }) return
        val symbolTable = SymbolTable()
        decls.forEach { symbolTable.add(it.key) }
        val env = Env()
        decls.forEach { env.define(it.key, it.value) }
        val expr = simplify(
            ExpressionWrapper(SimpleScope(symbolTable), memory.toString()).instantiate(env))
        Assert.assertEquals(simplify(memory), expr)
    }

    data class NamedSymbol(val _name: String) : Symbol {

        override fun getName(): String {
            return _name
        }

    }
}