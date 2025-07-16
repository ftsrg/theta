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
package hu.bme.mit.theta.btor2xcfa

import hu.bme.mit.theta.common.logging.UniqueWarningLogger
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.models.Btor2Circuit
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.xcfa.AssignStmtLabel
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.Btor2Passes

object Btor2XcfaBuilder {
  private var i: Int = 1

  fun btor2xcfa(parseContext: ParseContext, uniqueWarningLogger: UniqueWarningLogger): XCFA {
    check(Btor2Circuit.properties.isNotEmpty(), { "Circuit has no error property" })
    check(Btor2Circuit.properties.size <= 1, { "More than 1 property isn't allowed" })
    val ops = Btor2Circuit.ops.values.toList()
    for (i in 1 until ops.size) {
      check(ops[i].nid > ops[i - 1].nid, { "Ops are not in increasing order" })
    }
    val nodes = Btor2Circuit.nodes.values.toList()
    for (i in 1 until nodes.size) {
      check(nodes[i].nid > nodes[i - 1].nid, { "Nodes are not in increasing order" })
    }

    val xcfaBuilder = XcfaBuilder("Btor2XCFA")
    parseContext.addArithmeticTrait(ArithmeticTrait.BITWISE)

    val procBuilder = XcfaProcedureBuilder("main", Btor2Passes(parseContext, uniqueWarningLogger))
    xcfaBuilder.addEntryPoint(procBuilder, emptyList())
    procBuilder.createInitLoc()

    Btor2Circuit.nodes.forEach() {
      it.value.getVar()?.let { varDecl -> procBuilder.addVar(varDecl) }
    }

    var lastLoc = procBuilder.initLoc
    var newLoc = nextLoc(false, false, false)

    // add values to constants
    val constEdge =
      XcfaEdge(
        lastLoc,
        newLoc,
        SequenceLabel(
          Btor2Circuit.constants
            .map {
              AssignStmtLabel(
                it.value.getVar()!!.ref,
                BvLitExpr.of(it.value.value),
                metadata = EmptyMetaData,
              )
            }
            .toList()
        ),
        EmptyMetaData,
      )
    procBuilder.addEdge(constEdge)
    i++
    lastLoc = newLoc

    // Initializations
    newLoc = nextLoc(false, false, false)
    procBuilder.addLoc(newLoc)

    val edge =
      XcfaEdge(
        lastLoc,
        newLoc,
        SequenceLabel(
          Btor2Circuit.states
            .filter {
              if (it.value.getVar() != null && it.value.getVar()!!.name.startsWith("init_")) true
              else false
            }
            .map { StmtLabel(it.value.getStmt(), metadata = EmptyMetaData) }
            .toList()
        ),
        EmptyMetaData,
      )
    procBuilder.addEdge(edge)
    lastLoc = newLoc
    val loopHeadLoc = newLoc

    // Havoc initial value of input variables
    if (
      Btor2Circuit.states
        .filter { it.value.getVar()?.name?.startsWith("input_") == true }
        .isNotEmpty()
    ) {
      newLoc = nextLoc(false, false, false)
      procBuilder.addLoc(newLoc)
      val edge =
        XcfaEdge(
          lastLoc,
          newLoc,
          SequenceLabel(
            Btor2Circuit.states
              .filter {
                if (it.value.getVar() != null && it.value.getVar()!!.name.startsWith("input_")) true
                else false
              }
              .map { StmtLabel(it.value.getStmt(), metadata = EmptyMetaData) }
              .toList()
          ),
          EmptyMetaData,
        )
      procBuilder.addEdge(edge)
      lastLoc = newLoc
    }

    // Add operations
    Btor2Circuit.ops.forEach() {
      val loc = nextLoc(false, false, false)

      procBuilder.addLoc(loc)

      val edge = XcfaEdge(lastLoc, loc, StmtLabel(it.value.getStmt()), EmptyMetaData)
      procBuilder.addEdge(edge)
      lastLoc = loc
    }
    procBuilder.createErrorLoc()

    // Add Property
    val bad = Btor2Circuit.properties.values.first()

    procBuilder.addEdge(
      XcfaEdge(
        lastLoc,
        procBuilder.errorLoc.get(),
        StmtLabel(AssumeStmt.of(bad.getExpr())),
        EmptyMetaData,
      )
    )
    newLoc = nextLoc(false, false, false)
    procBuilder.addEdge(
      XcfaEdge(
        lastLoc,
        newLoc,
        StmtLabel(AssumeStmt.of(BoolExprs.Not(bad.getExpr()))),
        EmptyMetaData,
      )
    )
    lastLoc = newLoc

    // Close circuit (update state values with nexts, havoc otherwise)
    var nexts =
      Btor2Circuit.states.filter { it.value.getVar()?.name?.startsWith("next_") == true }.toList()

    nexts.forEach {
      newLoc = nextLoc(false, false, false)
      procBuilder.addEdge(XcfaEdge(lastLoc, newLoc, StmtLabel(it.second.getStmt()), EmptyMetaData))
      lastLoc = newLoc
    }
    procBuilder.addEdge(XcfaEdge(lastLoc, loopHeadLoc, metadata = EmptyMetaData))
    return xcfaBuilder.build()
  }

  private fun nextLoc(initial: Boolean, final: Boolean, error: Boolean): XcfaLocation {
    val loc = XcfaLocation("l${i}", initial, final, error, EmptyMetaData)
    i++
    return loc
  }
}
