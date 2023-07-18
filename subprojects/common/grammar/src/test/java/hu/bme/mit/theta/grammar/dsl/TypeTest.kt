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

import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType
import hu.bme.mit.theta.core.type.fptype.FpExprs.FpType
import hu.bme.mit.theta.core.type.functype.FuncExprs.Func
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.grammar.dsl.type.TypeWrapper
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized

@RunWith(Parameterized::class)
class TypeTest {

    @Parameterized.Parameter(0)
    lateinit var memory: Type

    @Parameterized.Parameter(1)
    lateinit var serialized: String

    companion object {

        @JvmStatic
        @Parameterized.Parameters
        fun data(): Collection<Array<Any>> {
            return listOf(
                arrayOf(Int(), "Int"),
                arrayOf(Rat(), "Rat"),
                arrayOf(Bool(), "Bool"),
                arrayOf(Func(Int(), Rat()), "(Func Int Rat)"),
                arrayOf(ArrayExprs.Array(Int(), Rat()), "(Array ([Int] -> Rat))"),
                arrayOf(BvType(32), "(Bv 32)"),
                arrayOf(FpType(12, 45), "(Fp 12 45)"),

                arrayOf(Func(Int(), ArrayExprs.Array(Int(), Rat())),
                    "(Func Int (Array ([Int] -> Rat)))"),
            )
        }
    }

    @Test
    fun testSerialize() {
        Assert.assertEquals(serialized, memory.toString())
    }

    @Test
    fun testDeserialize() {
        Assert.assertEquals(TypeWrapper(serialized).instantiate(), memory)
    }

    @Test
    fun testRoundTrip() {
        Assert.assertEquals(TypeWrapper(memory.toString()).instantiate(), memory)
    }

}