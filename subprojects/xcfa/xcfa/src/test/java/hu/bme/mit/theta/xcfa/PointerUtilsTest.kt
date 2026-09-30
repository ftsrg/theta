/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.inttype.IntExprs.Add
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Mod
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.procedure
import hu.bme.mit.theta.xcfa.model.xcfa
import hu.bme.mit.theta.xcfa.utils.pointsTo
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

private typealias PointerPartitions = List<Pair<Set<VarDecl<*>>, Set<LitExpr<*>>>>

class PointerUtilsTest {
  companion object {

    @JvmStatic
    fun data(): Collection<Array<Any>> =
      listOf(
        arrayOf(
          xcfa("xcfa1") {
            val main =
              procedure("main") {
                val x = "x" type Int()
                val p = "p" type Int()
                val q = "q" type Int()
                val r = "r" type Int()
                (init to "L") {
                  p.assign("0")
                  q.assign("1")
                  r.assign("2")
                }
                ("L" to final) {
                  x.assign("(deref p 0 Int)")
                  x.assign("(deref q 0 Int)")
                  x.assign("(deref r 0 Int)")
                }
              }
            main.start()
          },
          { partitions: PointerPartitions ->
            assertPartitionEquals(
              partitions,
              listOf(
                setOf("p") to setOf(Int(0)),
                setOf("q") to setOf(Int(1)),
                setOf("r") to setOf(Int(2)),
              ),
            )
          },
        ),
        arrayOf(
          xcfa("xcfa2") {
            val main =
              procedure("main") {
                val x = "x" type Int()
                val p = "p" type Int()
                val q = "q" type Int()
                val r = "r" type Int()
                (init to "L") {
                  p.assign("0")
                  q.assign("1")
                  nondet {
                    r.assign("0")
                    r.assign("2")
                  }
                }
                ("L" to final) {
                  x.assign("(deref p 0 Int)")
                  x.assign("(deref q 0 Int)")
                  x.assign("(deref r 0 Int)")
                }
              }
            main.start()
          },
          { partitions: PointerPartitions ->
            assertPartitionEquals(
              partitions,
              listOf(setOf("p", "r") to setOf(Int(0), Int(2)), setOf("q") to setOf(Int(1))),
            )
          },
        ),
        arrayOf(
          xcfa("xcfa3") {
            val main =
              procedure("main") {
                val x = "x" type Int()
                val p = "p" type Int()
                val q = "q" type Int()
                val r = "r" type Int()
                (init to "L") {
                  p.assign("0")
                  q.assign("1")
                  nondet {
                    r.assign("0")
                    r.assign("1")
                  }
                  q.assign("2")
                }
                ("L" to final) {
                  x.assign("(deref p 0 Int)")
                  x.assign("(deref q 0 Int)")
                  x.assign("(deref r 0 Int)")
                }
              }
            main.start()
          },
          { partitions: PointerPartitions ->
            assertPartitionEquals(
              partitions,
              listOf(setOf("p", "q", "r") to setOf(Int(0), Int(1), Int(2))),
            )
          },
        ),
      )

    private fun assertPartitionEquals(
      expected: PointerPartitions,
      actual: List<Pair<Set<String>, Set<LitExpr<*>>>>,
    ) {
      val varsInExpected = expected.flatMap { it.first }.associateBy { it.name }
      val transformedActual =
        actual.map { p ->
          val newVars = p.first.mapNotNull { varsInExpected[it] }.toSet()
          assertEquals(p.first.size, newVars.size, "Unmatched variables in ${p.first}")
          newVars to p.second
        }
      assertEquals(expected.toSet(), transformedActual.toSet())
    }
  }

  @Test
  fun valuesOfAnExpression() {
    val xcfa = data().first()[0] as XCFA
    val p = xcfa.procedures.flatMap { it.vars }.first { it.name == "p" }
    assertEquals(setOf(Int(1)), Add(cast(p.ref, Int()), Int(1)).pointsTo(xcfa))
    // A memory read has no variables to substitute, but its value is still unknown.
    val index = Mod(Dereference.of(Int(2), Int(0), Int()), Int(8))
    assertNull(index.pointsTo(xcfa))
  }

  @ParameterizedTest
  @MethodSource("data")
  fun pointerPartitionTest(xcfa: XCFA, expected: (PointerPartitions) -> Unit) {
    val pointerPartitions = xcfa.getPointerPartitions()
    expected(pointerPartitions)
  }
}
