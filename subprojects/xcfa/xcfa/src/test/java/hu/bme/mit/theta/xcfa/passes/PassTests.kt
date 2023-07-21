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

import hu.bme.mit.theta.core.type.fptype.FpExprs.FpType
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
                global = { "x" type Int() init "0"; "y" type Int() init "0" },
                passes = listOf(
                    NormalizePass(parseContext),
                    DeterministicPass(parseContext)
                ),
                input = {
                    (init to final) {
                        nondet {
                            havoc("x")
                            havoc("y")
                        }
                    }
                },
                output = {
                    (init to final) {
                        havoc("x")
                    }
                    (init to final) {
                        havoc("y")
                    }
                },
            ),
            PassTestData(
                global = { },
                passes = listOf(
                    NormalizePass(parseContext),
                    DeterministicPass(parseContext),
                    EliminateSelfLoops(parseContext),
                    LbePass(parseContext).also { LbePass.level = LbePass.LbeLevel.LBE_SEQ },
                ),
                input = {
                    (init to "L1") {
                        assume("true")
                    }
                    ("L1" to final) {
                        assume("false")
                    }
                },
                output = {
                    (init to final) {
                        assume("true")
                        assume("false")
                    }
                },
            ),
            PassTestData(
                global = { },
                passes = listOf(
                    EmptyEdgeRemovalPass(parseContext),
                    UnusedLocRemovalPass(parseContext)
                ),
                input = {
                    (init to "L1") {
                        nop()
                    }
                    ("L1" to "L2") {
                        nop()
                    }
                    ("L2" to final) {
                        nop()
                    }
                },
                output = {
                    (init to "L2") {
                        nop()
                    }
                    ("L2" to final) {
                        nop()
                    }
                },
            ),
            PassTestData(
                global = { },
                passes = listOf(
                    NormalizePass(parseContext),
                    DeterministicPass(parseContext),
                    ErrorLocationPass(false, parseContext)
                ),
                input = {
                    (init to final) {
                        "reach_error".invoke()
                    }
                },
                output = {
                    (init to err) { skip() }
                },
            ),
            PassTestData(
                global = { },
                passes = listOf(
                    NormalizePass(parseContext),
                    DeterministicPass(parseContext),
                    FinalLocationPass(false, parseContext),
                    UnusedLocRemovalPass(parseContext)
                ),
                input = {
                    (init to "L1") {
                        "abort".invoke()
                    }
                    (init to "L1") { skip() }
                    ("L1" to "L2") {
                        "exit".invoke()
                    }
                },
                output = {
                    (init to final) {
                        assume("false")
                    }
                    (init to "L1") { skip() }
                    ("L1" to final) {
                        assume("false")
                    }
                },
            ),
            PassTestData(
                global = { "x" type FpType(5, 11) init "0.0f"; },
                passes = listOf(
                    NormalizePass(parseContext),
                    DeterministicPass(parseContext),
                    FpFunctionsToExprsPass(parseContext),
                ),
                input = {
                    (init to final) {
                        "fabs".invoke("x", "x")
                    }
                    (init to final) {
                        "floor".invoke("x", "x")
                    }
                    (init to final) {
                        "fmax".invoke("x", "x", "x")
                    }
                    (init to final) {
                        "fmin".invoke("x", "x", "x")
                    }
                    (init to final) {
                        "sqrt".invoke("x", "x")
                    }
                    (init to final) {
                        "round".invoke("x", "x")
                    }
                    (init to final) {
                        "trunc".invoke("x", "x")
                    }
                    (init to final) {
                        "ceil".invoke("x", "x")
                    }
                },
                output = {
                    (init to final) {
                        "x".assign("(fpabs x)")
                    }
                    (init to final) {
                        "x".assign("(fproundtoint[RTN] x)")
                    }
                    (init to final) {
                        "x".assign("(fpmax x x)")
                    }
                    (init to final) {
                        "x".assign("(fpmin x x)")
                    }
                    (init to final) {
                        "x".assign("(fpsqrt x)")
                    }
                    (init to final) {
                        "x".assign("(fproundtoint[RNA] x)")
                    }
                    (init to final) {
                        "x".assign("(fproundtoint[RTZ] x)")
                    }
                    (init to final) {
                        "x".assign("(fproundtoint[RTP] x)")
                    }
                },
            ),
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