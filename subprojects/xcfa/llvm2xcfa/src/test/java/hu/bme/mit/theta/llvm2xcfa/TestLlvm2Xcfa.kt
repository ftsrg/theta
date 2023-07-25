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

package hu.bme.mit.theta.llvm2xcfa

import hu.bme.mit.theta.common.OsHelper
import hu.bme.mit.theta.llvm2xcfa.XcfaUtils.fromFile
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.io.File

class TestLlvm2Xcfa {

    companion object {

        @JvmStatic
        fun data(): Collection<Array<Any>> {
            return listOf(
                arrayOf("/c/every_inst.c"),
                arrayOf("/c/example_addition.c"),
                arrayOf("/c/example_binbitwiseop.c"),
                arrayOf("/c/example_branch.c"),
                arrayOf("/c/example_decl.c"),
                arrayOf("/c/example_func_param.c"),
                arrayOf("/c/example_global_scanf.c"),
                arrayOf("/c/example_struct.c"),
                arrayOf("/c/example_void_func.c"),
                arrayOf("/c/test_locks_14-2.c"),

                arrayOf("/c/dekker.i"),
                arrayOf("/c/00assignment.c"),
//                    arrayOf("/c/01cast.c"),
                arrayOf("/c/02types.c"),
                arrayOf("/c/03bitwise.c"),
//                    arrayOf("/c/04real.c"),
//                    arrayOf("/c/05math.c"),
                arrayOf("/c/06arrays.c"),
                arrayOf("/c/07arrayinit.c"),
                arrayOf("/c/08vararray.c"),
//                    arrayOf("/c/09struct.c"),
                arrayOf("/c/10ptr.c"),
                arrayOf("/c/11ptrs.c"),
                arrayOf("/c/12ptrtypes.c"),
                arrayOf("/c/13typedef.c"),
                arrayOf("/c/14ushort.c"),
                arrayOf("/c/15addition.c"),
                arrayOf("/c/16loop.c"),
//                    arrayOf("/c/17recursive.c"),
                arrayOf("/c/18multithread.c"),
                arrayOf("/c/19dportest.c"),
                arrayOf("/c/20testinline.c"),
                arrayOf("/c/21namecollision.c"),
//                    arrayOf("/c/22nondet.c"),
                arrayOf("/c/23overflow.c"),
            )
        }

        @BeforeAll
        @JvmStatic
        fun testOS() {
            Assumptions.assumeTrue(OsHelper.getOs() == OsHelper.OperatingSystem.LINUX) // only linux can handle llvm
        }
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testEfficient(filepath: String) {
        val fileName = javaClass.getResource(filepath)!!.file
        println("Parsing using LLVM: $filepath")

        fromFile(File(fileName), ArithmeticType.efficient)
    }

    @ParameterizedTest
    @MethodSource("data")
    fun testBitvector(filepath: String) {
        val fileName = javaClass.getResource(filepath)!!.file
        println("Parsing using LLVM: $filepath")

        fromFile(File(fileName), ArithmeticType.bitvector)
    }
}