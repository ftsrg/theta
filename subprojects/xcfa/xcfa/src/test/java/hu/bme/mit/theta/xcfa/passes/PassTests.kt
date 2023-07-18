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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class PassTests {


    class PassTestData(
        global: VarContext.() -> Unit,
        input: XcfaProcedureBuilderContext.() -> Unit,
        output: XcfaProcedureBuilderContext.() -> Unit,
        val passes: List<ProcedurePass>) : Arguments {

        private val builder = XcfaBuilder("").also { it.global(global) }
        private val inputBuilder = builder.procedure("", input).builder
        private val outputBuilder = builder.procedure("", output).builder


        override fun get(): Array<Any> = Arguments.of(inputBuilder, outputBuilder, passes).get()
    }

    companion object {

        private val dummyXcfa = xcfa("") {}
        private val parseContext = ParseContext()

        @JvmStatic
        val data: List<Arguments> = listOf(
            PassTestData(
                global = {
                    "x" type Int() init "0"
                    "y" type Int() init "0"
                },
                input = {
                    (init to final) {
                        nondet {
                            havoc("x")
                            havoc("y")
                        }
                    }
                },
                passes = listOf(
                    NormalizePass(parseContext),
                    DeterministicPass(parseContext)
                ),
                output = {
                    (init to final) {
                        havoc("x")
                    }
                    (init to final) {
                        havoc("y")
                    }
                },
            ),
            // TODO: add more tests for passes
        )

    }

    @ParameterizedTest
    @MethodSource("getData")
    fun testPass(input: XcfaProcedureBuilder, output: XcfaProcedureBuilder,
        passes: List<ProcedurePass>) {
        val actualOutput = passes.fold(input) { acc, procedurePass -> procedurePass.run(acc) }
            .build(dummyXcfa)
        val expectedOutput = output.build(dummyXcfa)
        assertEquals(expectedOutput, actualOutput)
    }

}