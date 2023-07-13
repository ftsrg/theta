package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.api.Assertions.*

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
                    NormalizePass(),
                    DeterministicPass()
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