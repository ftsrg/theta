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

import hu.bme.mit.theta.xcfa.cli.XcfaCli.Companion.main
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.util.*
import java.util.stream.Stream

class XcfaCliTest {
    companion object {

        @JvmStatic
        fun data(): Stream<Arguments> {
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
                Arguments.of("/c/litmustest/singlethread/09struct.c"),
                Arguments.of("/c/litmustest/singlethread/10ptr.c"),
                Arguments.of("/c/litmustest/singlethread/11ptrs.c"),
                Arguments.of("/c/litmustest/singlethread/12ptrtypes.c"),
                Arguments.of("/c/litmustest/singlethread/13typedef.c"),
                Arguments.of("/c/litmustest/singlethread/14ushort.c"))
        }
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testCParse(filePath: String) {
        main(arrayOf(
            "--input", javaClass.getResource(filePath)!!.path,
            "--parse-only"
        ))
    }

}
