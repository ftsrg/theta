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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.analysis.algorithm.Proof
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.svlib.SvLibProcedureExit
import hu.bme.mit.theta.frontend.svlib.SvLibTagMetadata
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssInvariants
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.passes.recordPassInvariants
import hu.bme.mit.theta.xcfa.passes.recordRemovedLocation
import java.io.File
import kotlin.io.path.createTempFile
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class SvLibWitnessWriterTest {

  private val x = Var("x", Int())
  private val y = Var("y", Int())
  private val t = Var("t", Int())
  private val g = Var("g", Int())
  private val parseContext = ParseContext().also { it.metadata.create(g, "isGlobal", true) }

  // procedure p with input x, output y and local t, whose whole body is tagged with `body`
  private val exit = SvLibProcedureExit("p", setOf(x), setOf(y)).also { it.tags += "body" }
  private val start = tagged("start", "body", liveVars = setOf(x))
  private val end = XcfaLocation("end", metadata = exit)

  @Test
  fun tagOfTheWholeBodyGetsAContract() {
    parseContext.recordRemovedLocation(XcfaLocation("unreachableEnd", metadata = exit), False())

    val witness =
      write(
        start to And(Eq(x.ref, Int(0)), Eq(g.ref, Int(1))),
        end to And(Eq(y.ref, Int(1)), Eq(g.ref, Int(1))),
      )

    assertEquals(
      """
      (
        (annotate-tag
          body
          :invariant
            (and (= x 0) (= g 1))
          :requires
            (and (= x 0) (= g 1))
          :ensures
            (and (= y 1) (= g 1))
        )
      )
      """
        .trimIndent() + "\n",
      witness,
    )
  }

  @Test
  fun otherTagsGetNoContract() {
    val witness = write(tagged("inner", "inner", liveVars = setOf(t)) to Eq(t.ref, Int(1)))

    assertEquals(
      """
      (
        (annotate-tag
          inner
          :invariant
            (= t 1)
        )
      )
      """
        .trimIndent() + "\n",
      witness,
    )
  }

  @Test
  fun contractIsProjectedToTheParametersAndGlobals() {
    val witness =
      write(
        tagged("start", "body", liveVars = setOf(y)) to And(Eq(x.ref, Int(0)), Eq(y.ref, Int(7))),
        end to And(Eq(y.ref, Int(1)), Eq(t.ref, Int(2))),
      )

    assertEquals(
      """
      (
        (annotate-tag
          body
          :invariant
            (exists ((x__proj_0 Int)) (and (= x__proj_0 0) (= y 7)))
          :requires
            (exists ((y__proj_0 Int)) (and (= x 0) (= y__proj_0 7)))
          :ensures
            (exists ((t__proj_0 Int)) (and (= y 1) (= t__proj_0 2)))
        )
      )
      """
        .trimIndent() + "\n",
      witness,
    )
  }

  @Test
  fun locationWithoutStatesIsUnreachable() {
    val unreached = tagged("unreached", "body", liveVars = setOf(x))
    parseContext.recordPassInvariants(unreached, Eq(t.ref, Int(0)))

    val witness =
      write(
        LocationInvariants(
          mapOf(unreached to emptyList(), end to listOf(PredState.of(Eq(y.ref, Int(1)))))
        )
      )

    assertEquals(
      """
      (
        (annotate-tag
          body
          :invariant
            false
          :requires
            false
          :ensures
            (= y 1)
        )
      )
      """
        .trimIndent() + "\n",
      witness,
    )
  }

  @Test
  fun locationWithUnknownStatesKeepsItsPassInvariants() {
    val known = tagged("known", "inner", liveVars = setOf(t))
    val unknown = tagged("unknown", "inner", liveVars = setOf(t))
    parseContext.recordPassInvariants(unknown, Eq(t.ref, Int(2)))

    val witness = write(DssInvariants(mapOf(known to listOf(Eq(t.ref, Int(1))), unknown to null)))

    assertEquals(
      """
      (
        (annotate-tag
          inner
          :invariant
            (or (= t 1) (= t 2))
        )
      )
      """
        .trimIndent() + "\n",
      witness,
    )
  }

  private fun tagged(name: String, tag: String, liveVars: Set<VarDecl<*>>) =
    XcfaLocation(name, metadata = SvLibTagMetadata(setOf(tag), "p").also { it.liveVars = liveVars })

  private fun write(vararg invariants: Pair<XcfaLocation, Expr<BoolType>>) =
    write(LocationInvariants(invariants.associate { (l, inv) -> l to listOf(PredState.of(inv)) }))

  private fun write(proof: Proof): String {
    val witnessFile = createTempFile(suffix = ".svlib").toFile().also(File::deleteOnExit)
    SvLibWitnessWriter()
      .writeWitness(
        SafetyResult.safe<Proof, Nothing>(proof),
        File("input.svlib"),
        XcfaProperty(ErrorDetection.ERROR_LOCATION),
        Z3LegacySolverFactory.getInstance(),
        parseContext,
        witnessFile,
        "",
        null,
        NullLogger.getInstance(),
      )
    return witnessFile.readText()
  }
}
