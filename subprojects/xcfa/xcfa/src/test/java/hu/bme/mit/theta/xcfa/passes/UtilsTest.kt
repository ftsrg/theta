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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.stmt.Stmts.*
import hu.bme.mit.theta.core.type.inttype.IntExprs.Add
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.simplify
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class UtilsTest {

  /**
   * The passes that lower a call match its arguments syntactically, so simplification must hand
   * back the argument itself rather than a wrapper carrying the same C type. A wrapped pointer made
   * `memset` unrecognizable, and the `InvokeLabel` left behind was refused by the monolithic
   * backends.
   */
  @Test
  fun simplifyKeepsCallArgumentsUnwrapped() {
    val parseContext = ParseContext()
    val p = Var("p", Int())
    val signed = CSignedInt(null, parseContext)
    parseContext.metadata.create(p.ref, "cType", signed)
    // An argument that folds back to `p`, but whose own recorded type differs from `p`'s: this is
    // what used to make the carried-over type wrap the result instead of just labelling it.
    val argument = Add(listOf(p.ref, Int(0)))
    parseContext.metadata.create(argument, "cType", CPointer(null, signed, parseContext))
    val label = InvokeLabel("memset", listOf(argument), EmptyMetaData, mapOf())

    val simplified = label.simplify(MutableValuation(), parseContext) as InvokeLabel

    Assertions.assertEquals(p.ref, simplified.params[0])
  }

  companion object {

    private val x = Var("x", Int())
    private val y = Var("y", Int())
    private val xPrime = Var("x'", Int())
    private val map: Map<Decl<*>, VarDecl<*>> = mapOf(Pair(x, xPrime))

    @JvmStatic
    fun getLabels(): List<Arguments> =
      listOf(
        Arguments.of(
          InvokeLabel("", listOf(x.ref, y.ref), EmptyMetaData),
          InvokeLabel("", listOf(xPrime.ref, y.ref), EmptyMetaData),
        ),
        Arguments.of(JoinLabel(x, EmptyMetaData), JoinLabel(xPrime, EmptyMetaData)),
        Arguments.of(
          NondetLabel(setOf(NopLabel), EmptyMetaData),
          NondetLabel(setOf(NopLabel), EmptyMetaData),
        ),
        Arguments.of(
          SequenceLabel(listOf(NopLabel), EmptyMetaData),
          SequenceLabel(listOf(NopLabel), EmptyMetaData),
        ),
        Arguments.of(AtomicBeginLabel(), AtomicBeginLabel()),
        Arguments.of(MutexLockLabel(x), MutexLockLabel(xPrime)),
        Arguments.of(
          StartLabel("", listOf(x.ref), y, EmptyMetaData),
          StartLabel("", listOf(xPrime.ref), y, EmptyMetaData),
        ),
        Arguments.of(
          ReturnLabel(JoinLabel(x, EmptyMetaData)),
          ReturnLabel(JoinLabel(xPrime, EmptyMetaData)),
        ),
        Arguments.of(StmtLabel(Assign(x, y.ref)), StmtLabel(Assign(xPrime, y.ref))),
        Arguments.of(StmtLabel(Havoc(x)), StmtLabel(Havoc(xPrime))),
        Arguments.of(StmtLabel(Assume(Eq(x.ref, y.ref))), StmtLabel(Assume(Eq(xPrime.ref, y.ref)))),
        Arguments.of(StmtLabel(Skip()), StmtLabel(Skip())),
      )
  }

  @ParameterizedTest
  @MethodSource("getLabels")
  fun testChangeVars(labelIn: XcfaLabel, labelExp: XcfaLabel) {
    Assertions.assertEquals(labelExp, labelIn.changeVars(map))
  }
}
