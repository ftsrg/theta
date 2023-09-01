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

package hu.bme.mit.theta.c2xcfa

import hu.bme.mit.theta.frontend.ParseContext
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.IOException

@RunWith(Parameterized::class)
class TestFrontendXcfaBuilder {

    @Parameterized.Parameter(0)
    lateinit var filepath: String

    companion object {

        @JvmStatic
        @Parameterized.Parameters
        fun data(): Collection<Array<Any>> {
            return listOf(
                arrayOf("/00assignment.c"),
                arrayOf("/01cast.c"),
                arrayOf("/02types.c"),
                arrayOf("/03bitwise.c"),
                arrayOf("/04real.c"),
                arrayOf("/05math.c"),
                arrayOf("/06arrays.c"),
                arrayOf("/07arrayinit.c"),
                arrayOf("/08vararray.c"),
                arrayOf("/09struct.c"),
                arrayOf("/10ptr.c"),
                arrayOf("/11ptrs.c"),
                arrayOf("/12ptrtypes.c"),
                arrayOf("/13typedef.c"),
                arrayOf("/14ushort.c"),
                arrayOf("/15addition.c"),
                arrayOf("/16loop.c"),
//                    arrayOf("/17recursive.c"),
                arrayOf("/18multithread.c"),
                arrayOf("/19dportest.c"),
                arrayOf("/20testinline.c"),
                arrayOf("/21namecollision.c"),
                arrayOf("/22nondet.c"),
                arrayOf("/23exotic.c"),
            )
        }
    }

    @Test
    @Throws(IOException::class)
    fun testReachability() {

        val stream = javaClass.getResourceAsStream(filepath)

        getXcfaFromC(stream!!, ParseContext(), false, false)
    }

    @Test
    @Throws(IOException::class)
    fun testOverflow() {

        val stream = javaClass.getResourceAsStream(filepath)

        getXcfaFromC(stream!!, ParseContext(), false, true)
    }
}