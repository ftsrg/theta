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
package hu.bme.mit.theta.xcfa.cli

import hu.bme.mit.theta.frontend.chc.ChcFrontend
import hu.bme.mit.theta.xcfa.cli.XcfaCli.Companion.main
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.util.*
import java.util.stream.Stream
import kotlin.io.path.absolutePathString
import kotlin.io.path.createTempDirectory
import kotlin.io.path.exists

class XcfaCliVerifyTest {
    companion object {


        @JvmStatic
        fun cFiles(): Stream<Arguments> {
            return Stream.of(
                Arguments.of("/c/dekker.i", "--search DFS --por-level SPOR"),
                Arguments.of("/c/litmustest/singlethread/00assignment.c", null),
                Arguments.of("/c/litmustest/singlethread/01cast.c", null),
                Arguments.of("/c/litmustest/singlethread/02types.c", null),
                Arguments.of("/c/litmustest/singlethread/03bitwise.c", null),
                Arguments.of("/c/litmustest/singlethread/04real.c", null),
//                Arguments.of("/c/litmustest/singlethread/05math.c", null), // too resource-intensive
                Arguments.of("/c/litmustest/singlethread/06arrays.c", null),
                Arguments.of("/c/litmustest/singlethread/07arrayinit.c", null),
                Arguments.of("/c/litmustest/singlethread/08vararray.c", null),
//                    Arguments.of("/c/litmustest/singlethread/09struct.c", null),
//                    Arguments.of("/c/litmustest/singlethread/10ptr.c", null),
//                    Arguments.of("/c/litmustest/singlethread/11ptrs.c", null),
//                    Arguments.of("/c/litmustest/singlethread/12ptrtypes.c", null),
                Arguments.of("/c/litmustest/singlethread/13typedef.c", "--domain PRED_CART"),
                Arguments.of("/c/litmustest/singlethread/14ushort.c", null),
                Arguments.of("/c/litmustest/singlethread/15addition.c", null),
                Arguments.of("/c/litmustest/singlethread/16loop.c", null),
                Arguments.of("/c/litmustest/singlethread/17recursive.c", null),
                Arguments.of("/c/litmustest/singlethread/18multithread.c", "--search DFS --por-level SPOR"),
                Arguments.of("/c/litmustest/singlethread/19dportest.c", "--search DFS --por-level SPOR"),
                Arguments.of("/c/litmustest/singlethread/20testinline.c", null),
                Arguments.of("/c/litmustest/singlethread/21namecollision.c", null),
                Arguments.of("/c/litmustest/singlethread/22nondet.c", null),
                Arguments.of("/c/litmustest/singlethread/23overflow.c", "--domain PRED_CART"),
            )
        }

        @JvmStatic
        fun cFilesShort(): Stream<Arguments> {
            return Stream.of(
                Arguments.of("/c/dekker.i", "--search DFS --por-level SPOR"),
                Arguments.of("/c/litmustest/singlethread/00assignment.c", null),
                Arguments.of("/c/litmustest/singlethread/01cast.c", null),
                Arguments.of("/c/litmustest/singlethread/02types.c", null),
                Arguments.of("/c/litmustest/singlethread/03bitwise.c", null),
                Arguments.of("/c/litmustest/singlethread/04real.c", null),
            )
        }

        @JvmStatic
        fun chcFiles(): Stream<Arguments> {
            return Stream.of(
                Arguments.of("/chc/chc-LIA-Lin_000.smt2", ChcFrontend.ChcTransformation.FORWARD, "--domain PRED_CART"),
                Arguments.of("/chc/chc-LIA-Arrays_000.smt2", ChcFrontend.ChcTransformation.BACKWARD,
                    "--domain PRED_CART"),
            )
        }
    }

    @ParameterizedTest
    @MethodSource("cFiles")
    fun testCVerifyDirect(filePath: String, extraArgs: String?) {
        val params = arrayOf(
            "--input-type", "C",
            "--input", javaClass.getResource(filePath)!!.path,
            "--stacktrace",
            *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        )
        main(params)
    }

    @ParameterizedTest
    @MethodSource("cFilesShort")
    fun testCVerifyServer(filePath: String, extraArgs: String?) {
        val params = arrayOf(
            "--input-type", "C",
            "--strategy", "SERVER_DEBUG",
            "--input", javaClass.getResource(filePath)!!.path,
            "--stacktrace",
            *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        )
        try {
            main(params)
        } catch (e: IllegalStateException) {
            if (!e.message.equals("Done debugging")) {
                throw e
            }
        }
    }

    @ParameterizedTest
    @MethodSource("cFilesShort")
    fun testCVerifyPortfolio(filePath: String, extraArgs: String?) {
        val params = arrayOf(
            "--input-type", "C",
            "--strategy", "PORTFOLIO",
            "--debug",
            "--portfolio", javaClass.getResource("/simple.kts")!!.path,
            "--input", javaClass.getResource(filePath)!!.path,
            "--stacktrace",
        )
        try {
            main(params)
        } catch (e: Throwable) {
            if (!e.toString().contains("Done debugging")) {
                throw e
            }
        }
    }

    @ParameterizedTest
    @MethodSource("cFiles")
    fun testCWitness(filePath: String, extraArgs: String?) {
        val temp = createTempDirectory()
        val params = arrayOf(
            "--input-type", "C",
            "--input", javaClass.getResource(filePath)!!.path,
            "--stacktrace",
            *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
            "--output-results",
            "--output-directory", temp.absolutePathString()
        )
        main(params)
        Assertions.assertTrue(temp.resolve("xcfa.json").exists())
        Assertions.assertTrue(temp.resolve("arg-true.dot").exists() || temp.resolve("arg-false.dot").exists())
        temp.toFile().deleteRecursively()
    }

    @ParameterizedTest
    @MethodSource("chcFiles")
    fun testCHCVerify(filePath: String, chcTransformation: ChcFrontend.ChcTransformation, extraArgs: String?) {
        main(arrayOf(
            "--input-type", "CHC",
            "--chc-transformation", chcTransformation.toString(),
            "--input", javaClass.getResource(filePath)!!.path,
            "--stacktrace",
            *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        ))
    }

}
