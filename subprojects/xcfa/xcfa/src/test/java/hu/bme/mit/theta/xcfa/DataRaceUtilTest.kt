/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa

import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.*
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.isDataRacePossible
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class DataRaceUtilTest {

  companion object {

    private class DataRaceUtilTestData(
      private val model: XCFA,
      private val check: (XCFA) -> Unit,
      private val expectedDataRacePossible: Boolean,
    ) : Arguments {

      override fun get(): Array<Any> = Arguments.of(model, check, expectedDataRacePossible).get()
    }

    @JvmStatic
    private val data: List<Arguments>
      get() =
        listOf(
          DataRaceUtilTestData(
            model =
              xcfa("") {
                global {
                  "x" type Int() init "0"
                  "ERR" type Int() init "0"
                }
                val thr1 =
                  procedure("thr1") {
                    (init to "L") {
                      atomic_begin()
                      "x" assign "1"
                      atomic_end()
                    }
                    ("L" to final) {
                      atomic_begin()
                      "x" assign "2"
                      atomic_end()
                    }
                  }
                val thr2 =
                  procedure("thr2") {
                    "i" type Int()
                    "j" type Int()
                    (init to "L1") {
                      atomic_begin()
                      "i" assign "x"
                      atomic_end()
                    }
                    ("L1" to "L2") {
                      atomic_begin()
                      "j" assign "x"
                      atomic_end()
                    }
                    ("L2" to final) {
                      assume("(/= i j)")
                      "ERR" assign "1"
                    }
                    ("L2" to final) { assume("(= i j)") }
                  }
                val main =
                  procedure("main") {
                    "t1" type Int()
                    "t2" type Int()
                    (init to "L1") {
                      "t1".start(thr1)
                      "t2".start(thr2)
                    }
                    ("L1" to "L2") {
                      "t1".join()
                      "t2".join()
                    }
                    ("L2" to err) { assume("(/= ERR 0)") }
                    ("L2" to final) { assume("(= ERR 0)") }
                  }
                main.start()
              },
            check = { transformed ->
              assertTrue(transformed.globalVars.none { it.wrappedVar.name == "_write_flag_x" })
              assertTrue(transformed.globalVars.none { it.wrappedVar.name == "_read_flag_x" })
              assertTrue(
                transformed.procedures.all {
                  it.errorLoc.isEmpty || it.errorLoc.get().incomingEdges.isEmpty()
                }
              )
            },
            expectedDataRacePossible = false,
          ),
          DataRaceUtilTestData(
            model =
              xcfa("") {
                global {
                  "x" type Int() init "0"
                  "ERR" type Int() init "0"
                }
                val thr1 =
                  procedure("thr1") {
                    (init to "L") {
                      atomic_begin()
                      "x" assign "1"
                      atomic_end()
                    }
                    ("L" to final) {
                      atomic_begin()
                      "x" assign "2"
                      atomic_end()
                    }
                  }
                val thr2 =
                  procedure("thr2") {
                    "i" type Int()
                    "j" type Int()
                    (init to "L1") {
                      atomic_begin()
                      "i" assign "x"
                      atomic_end()
                    }
                    ("L1" to "L2") {
                      "j" assign "x" // atomic block omitted here
                    }
                    ("L2" to final) {
                      assume("(/= i j)")
                      "ERR" assign "1"
                    }
                    ("L2" to final) { assume("(= i j)") }
                  }
                val main =
                  procedure("main") {
                    "t1" type Int()
                    "t2" type Int()
                    (init to "L1") {
                      "t1".start(thr1)
                      "t2".start(thr2)
                    }
                    ("L1" to "L2") {
                      "t1".join()
                      "t2".join()
                    }
                    ("L2" to err) { assume("(/= ERR 0)") }
                    ("L2" to final) { assume("(= ERR 0)") }
                  }
                main.start()
              },
            check = { transformed ->
              assertNotNull(transformed.globalVars.find { it.wrappedVar.name == "_write_flag_x" })
              assertNotNull(transformed.globalVars.find { it.wrappedVar.name == "_read_flag_x" })
              assertTrue(
                transformed.procedures.all {
                  when (it.name) {
                    "main" -> it.errorLoc.isEmpty || it.errorLoc.get().incomingEdges.isEmpty()
                    else ->
                      it.errorLoc.get().incomingEdges.isNotEmpty() &&
                        it.errorLoc.get().incomingEdges.all { e ->
                          "_write_flag_x" in e.collectVarsWithAccessType().map { a -> a.key.name }
                        }
                  }
                }
              )
            },
            expectedDataRacePossible = true,
          ),
        )
  }

  @ParameterizedTest
  @MethodSource("getData")
  fun testDataRaceUtils(xcfa: XCFA, check: (XCFA) -> Unit, expectedDataRacePossible: Boolean) {
    val dataRacePossible = isDataRacePossible(xcfa)
    Assertions.assertEquals(expectedDataRacePossible, dataRacePossible)

    val property = XcfaProperty(ErrorDetection.DATA_RACE)
    Assertions.assertEquals(ErrorDetection.DATA_RACE, property.verifiedProperty)
    val actualTransformed =
      xcfa.optimizeFurther(
        ProcedurePassManager(
          listOf(
            DataRaceToReachabilityPass(property, true),
            UnusedLocRemovalPass(),
            NormalizePass(),
            DeterministicPass(),
          )
        )
      )
    Assertions.assertEquals(ErrorDetection.ERROR_LOCATION, property.verifiedProperty)
    check(actualTransformed)
  }
}
