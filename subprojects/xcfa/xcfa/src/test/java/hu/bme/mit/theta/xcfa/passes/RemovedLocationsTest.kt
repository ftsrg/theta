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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.procedures.InlinedProcedureRemovalPass
import hu.bme.mit.theta.xcfa.passes.structure.RemoveDeadEnds
import hu.bme.mit.theta.xcfa.passes.structure.UnusedLocRemovalPass
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class RemovedLocationsTest {

  private class KeptLocation : MetaData() {
    override fun combine(other: MetaData) = this

    override fun isSubstantial() = false

    override fun keepsLocation() = true
  }

  private val xcfaBuilder = XcfaBuilder("")
  private val builder = procedure("main")
  private val head = XcfaLocation("head", metadata = KeptLocation())
  private val body = XcfaLocation("body", metadata = EmptyMetaData)
  private val orphan = XcfaLocation("orphan", metadata = KeptLocation())

  init {
    // `head` and `body` form a dead-end loop, `orphan` is unreachable
    builder.addEdge(XcfaEdge(builder.initLoc, builder.finalLoc.get(), NopLabel, EmptyMetaData))
    builder.addEdge(XcfaEdge(builder.initLoc, head, NopLabel, EmptyMetaData))
    builder.addEdge(XcfaEdge(head, body, NopLabel, EmptyMetaData))
    builder.addEdge(XcfaEdge(body, head, NopLabel, EmptyMetaData))
    builder.addEdge(XcfaEdge(orphan, builder.finalLoc.get(), NopLabel, EmptyMetaData))
  }

  @Test
  fun nothingIsRecordedByDefault() {
    val parseContext = ParseContext()
    RemoveDeadEnds(parseContext).runChecked(builder)
    UnusedLocRemovalPass().runChecked(builder)

    assertEquals(1, builder.getEdges().size)
    assertTrue(parseContext.removedLocations().isEmpty())
  }

  @Test
  fun removedDeadEndsKeepTheirPassInvariantsAndUnreachableOnesAreFalse() {
    val parseContext = ParseContext()
    val fact = Eq(Var("x", Int()).ref, Int(0))
    parseContext.recordPassInvariants(head, fact)
    RemoveDeadEnds(parseContext, recordPassInvariants = true).runChecked(builder)

    assertEquals(setOf(head to fact, orphan to False()), parseContext.removedLocations().toSet())
  }

  @Test
  fun unreachableLocationsRemovedAsUnusedAreFalse() {
    val parseContext = ParseContext()
    UnusedLocRemovalPass(parseContext).runChecked(builder)

    assertEquals(setOf(orphan to False()), parseContext.removedLocations().toSet())
  }

  @Test
  fun locationsOfRemovedProceduresAreFalse() {
    val parseContext = ParseContext()
    xcfaBuilder.addEntryPoint(procedure("entry"), listOf())
    val unused = procedure("unused")
    val kept = XcfaLocation("kept", metadata = KeptLocation())
    unused.addEdge(XcfaEdge(unused.initLoc, kept, NopLabel, EmptyMetaData))
    unused.addEdge(XcfaEdge(kept, unused.finalLoc.get(), NopLabel, EmptyMetaData))
    InlinedProcedureRemovalPass(parseContext).runChecked(unused)

    assertFalse(unused in xcfaBuilder.getProcedures())
    assertEquals(setOf(kept to False()), parseContext.removedLocations().toSet())
  }

  private fun procedure(name: String) =
    XcfaProcedureBuilder(name, ProcedurePassManager()).also {
      xcfaBuilder.addProcedure(it)
      it.createInitLoc()
      it.createFinalLoc()
      it.createErrorLoc()
    }
}
