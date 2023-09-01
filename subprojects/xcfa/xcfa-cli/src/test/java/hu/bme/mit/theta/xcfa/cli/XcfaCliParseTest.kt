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
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.util.*
import java.util.stream.Stream
import kotlin.io.path.createTempDirectory

class XcfaCliParseTest {
    companion object {

        @JvmStatic
        fun cFiles(): Stream<Arguments> {
            return Stream.of(
                Arguments.of("/c/dekker.i"),
                Arguments.of("/c/litmustest/singlethread/00assignment.c"),
                Arguments.of("/c/litmustest/singlethread/01cast.c"),
                Arguments.of("/c/litmustest/singlethread/02types.c"),
                Arguments.of("/c/litmustest/singlethread/03bitwise.c"),
                Arguments.of("/c/litmustest/singlethread/04real.c"),
                Arguments.of("/c/litmustest/singlethread/05math.c"),
                Arguments.of("/c/litmustest/singlethread/06arrays.c"),
                Arguments.of("/c/litmustest/singlethread/07arrayinit.c"),
                Arguments.of("/c/litmustest/singlethread/08vararray.c"),
//                    Arguments.of("/c/litmustest/singlethread/09struct.c"),
//                    Arguments.of("/c/litmustest/singlethread/10ptr.c"),
//                    Arguments.of("/c/litmustest/singlethread/11ptrs.c"),
//                    Arguments.of("/c/litmustest/singlethread/12ptrtypes.c"),
                Arguments.of("/c/litmustest/singlethread/13typedef.c"),
                Arguments.of("/c/litmustest/singlethread/14ushort.c"),
                Arguments.of("/c/litmustest/singlethread/15addition.c"),
                Arguments.of("/c/litmustest/singlethread/16loop.c"),
                Arguments.of("/c/litmustest/singlethread/17recursive.c"),
                Arguments.of("/c/litmustest/singlethread/18multithread.c"),
                Arguments.of("/c/litmustest/singlethread/19dportest.c"),
                Arguments.of("/c/litmustest/singlethread/20testinline.c"),
                Arguments.of("/c/litmustest/singlethread/21namecollision.c"),
                Arguments.of("/c/litmustest/singlethread/22nondet.c"),
                Arguments.of("/c/litmustest/singlethread/23overflow.c"),
            )
        }

        @JvmStatic
        fun llvmFiles(): Stream<Arguments> {
            return Stream.of(
                Arguments.of("/c/dekker.i"),
                Arguments.of("/c/litmustest/singlethread/00assignment.c"),
//                Arguments.of("/c/litmustest/singlethread/01cast.c"),
                Arguments.of("/c/litmustest/singlethread/02types.c"),
                Arguments.of("/c/litmustest/singlethread/03bitwise.c"),
//                Arguments.of("/c/litmustest/singlethread/04real.c"),
//                Arguments.of("/c/litmustest/singlethread/05math.c"),
                Arguments.of("/c/litmustest/singlethread/06arrays.c"),
                Arguments.of("/c/litmustest/singlethread/07arrayinit.c"),
                Arguments.of("/c/litmustest/singlethread/08vararray.c"),
//                    Arguments.of("/c/litmustest/singlethread/09struct.c"),
//                    Arguments.of("/c/litmustest/singlethread/10ptr.c"),
//                    Arguments.of("/c/litmustest/singlethread/11ptrs.c"),
//                    Arguments.of("/c/litmustest/singlethread/12ptrtypes.c"),
                Arguments.of("/c/litmustest/singlethread/13typedef.c"),
                Arguments.of("/c/litmustest/singlethread/14ushort.c"),
                Arguments.of("/c/litmustest/singlethread/15addition.c"),
                Arguments.of("/c/litmustest/singlethread/16loop.c"),
//                Arguments.of("/c/litmustest/singlethread/17recursive.c"),
                Arguments.of("/c/litmustest/singlethread/18multithread.c"),
                Arguments.of("/c/litmustest/singlethread/19dportest.c"),
                Arguments.of("/c/litmustest/singlethread/20testinline.c"),
                Arguments.of("/c/litmustest/singlethread/21namecollision.c"),
//                Arguments.of("/c/litmustest/singlethread/22nondet.c"),
                Arguments.of("/c/litmustest/singlethread/23overflow.c"),
            )
        }

        @JvmStatic
        fun chcFiles(): Stream<Arguments> {
            return Stream.of(
                Arguments.of("/chc/chc-LIA-Arrays_000.smt2", ChcFrontend.ChcTransformation.PORTFOLIO),
                Arguments.of("/chc/chc-LIA-Lin-Arrays_000.smt2", ChcFrontend.ChcTransformation.PORTFOLIO),
                Arguments.of("/chc/chc-LIA-Lin_000.smt2", ChcFrontend.ChcTransformation.PORTFOLIO),
                Arguments.of("/chc/chc-LIA-nonlin-Arrays-nonrecADT_000.smt2", ChcFrontend.ChcTransformation.PORTFOLIO),
                Arguments.of("/chc/chc-LIA_000.smt2", ChcFrontend.ChcTransformation.PORTFOLIO),

//                Arguments.of("/chc/chc-LIA-Arrays_000.smt2", ChcFrontend.ChcTransformation.FORWARD), // nonlin
                Arguments.of("/chc/chc-LIA-Lin-Arrays_000.smt2", ChcFrontend.ChcTransformation.FORWARD),
                Arguments.of("/chc/chc-LIA-Lin_000.smt2", ChcFrontend.ChcTransformation.FORWARD),
                Arguments.of("/chc/chc-LIA-nonlin-Arrays-nonrecADT_000.smt2", ChcFrontend.ChcTransformation.FORWARD),
//                Arguments.of("/chc/chc-LIA_000.smt2", ChcFrontend.ChcTransformation.FORWARD), // nonlin

                Arguments.of("/chc/chc-LIA-Arrays_000.smt2", ChcFrontend.ChcTransformation.BACKWARD),
                Arguments.of("/chc/chc-LIA-Lin-Arrays_000.smt2", ChcFrontend.ChcTransformation.BACKWARD),
                Arguments.of("/chc/chc-LIA-Lin_000.smt2", ChcFrontend.ChcTransformation.BACKWARD),
                Arguments.of("/chc/chc-LIA-nonlin-Arrays-nonrecADT_000.smt2", ChcFrontend.ChcTransformation.BACKWARD),
                Arguments.of("/chc/chc-LIA_000.smt2", ChcFrontend.ChcTransformation.BACKWARD),
            )
        }

        @JvmStatic
        fun dslFiles(): Stream<Arguments> {
            return Stream.of(
                Arguments.of("/dsl/async.xcfa.kts"),
                Arguments.of("/dsl/sync.xcfa.kts"),
            )
        }

        @JvmStatic
        fun jsonFiles(): Stream<Arguments> {
            return Stream.of(
                Arguments.of("/json/00assignment.c.json"),
                Arguments.of("/json/01cast.c.json"),
                Arguments.of("/json/02types.c.json"),
                Arguments.of("/json/03bitwise.c.json"),
                Arguments.of("/json/04real.c.json"),
                Arguments.of("/json/05math.c.json"),
                Arguments.of("/json/06arrays.c.json"),
                Arguments.of("/json/07arrayinit.c.json"),
                Arguments.of("/json/08vararray.c.json"),
//                    Arguments.of("/json/09struct.c.json"),
//                    Arguments.of("/json/10ptr.c.json"),
//                    Arguments.of("/json/11ptrs.c.json"),
//                    Arguments.of("/json/12ptrtypes.c.json"),
                Arguments.of("/json/13typedef.c.json"),
                Arguments.of("/json/14ushort.c.json"),
                Arguments.of("/json/15addition.c.json"),
                Arguments.of("/json/16loop.c.json"),
                Arguments.of("/json/17recursive.c.json"),
                Arguments.of("/json/18multithread.c.json"),
                Arguments.of("/json/19dportest.c.json"),
                Arguments.of("/json/20testinline.c.json"),
                Arguments.of("/json/21namecollision.c.json"),
                Arguments.of("/json/22nondet.c.json"),
                Arguments.of("/json/23overflow.c.json"),
            )
        }
    }

    @ParameterizedTest
    @MethodSource("cFiles")
    fun testCParse(filePath: String) {
        main(arrayOf(
            "--input-type", "C",
            "--input", javaClass.getResource(filePath)!!.path,
            "--parse-only", "--stacktrace"
        ))
    }

//    @ParameterizedTest
//    @MethodSource("llvmFiles")
//    fun testLLVMParse(filePath: String) {
//        if (OsHelper.getOs() == OsHelper.OperatingSystem.LINUX) {
//            main(arrayOf(
//                "--input-type", "LLVM",
//                "--input", javaClass.getResource(filePath)!!.path,
//                "--parse-only", "--stacktrace"
//            ))
//        }
//    }

    @ParameterizedTest
    @MethodSource("chcFiles")
    fun testCHCParse(filePath: String, chcTransformation: ChcFrontend.ChcTransformation) {
        main(arrayOf(
            "--input-type", "CHC",
            "--chc-transformation", chcTransformation.toString(),
            "--input", javaClass.getResource(filePath)!!.path,
            "--parse-only",
            "--stacktrace",
        ))
    }

    @ParameterizedTest
    @MethodSource("dslFiles")
    fun testDSLParse(filePath: String) {
        main(arrayOf(
            "--input-type", "DSL",
            "--input", javaClass.getResource(filePath)!!.path,
            "--parse-only",
            "--stacktrace",
        ))
    }

    @ParameterizedTest
    @MethodSource("jsonFiles")
    fun testJSONParse(filePath: String) {
        main(arrayOf(
            "--input-type", "JSON",
            "--input", javaClass.getResource(filePath)!!.path,
            "--parse-only",
            "--stacktrace",
        ))
    }

    @ParameterizedTest
    @MethodSource("cFiles")
    fun testJSONParseRoundTrip(filePath: String) {
        val temp = createTempDirectory()
        main(arrayOf(
            "--input-type", "C",
            "--input", javaClass.getResource(filePath)!!.path,
            "--parse-only",
            "--stacktrace",
            "--output-results",
            "--output-directory", temp.toAbsolutePath().toString(),
        ))
        val xcfaJson = temp.resolve("xcfa.json").toFile()
        main(arrayOf(
            "--input-type", "JSON",
            "--input", xcfaJson.absolutePath.toString(),
            "--parse-only",
            "--stacktrace",
        ))
        temp.toFile().deleteRecursively()
    }

}
