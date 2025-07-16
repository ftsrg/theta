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

import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.frontend.models.Btor2Circuit
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager

object Btor2XcfaBuilder {
  private var i: Int = 1

  fun btor2xcfa(circuit: Btor2Circuit): XCFA {
    // checks fontos: nodes, ops, properties csak 1 legyen
    check(Btor2Circuit.properties.size != 0, { "Circuit has no error property" })
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
    val procBuilder = XcfaProcedureBuilder("main", Btor2Pass())
    xcfaBuilder.addEntryPoint(procBuilder, emptyList())
    procBuilder.createInitLoc()

    Btor2Circuit.nodes.forEach() {
      it.value.getVar()?.let { varDecl -> procBuilder.addVar(varDecl) }
    }
    ///////////////////////////////////////////////
    // Initek
    var lastLoc = procBuilder.initLoc
    var newLoc = nextLoc(false, false, false)
    // initekhez
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
    i++
    lastLoc = newLoc
    ///////////////////////////////////////////////
    // Havoc változók
    // Miután felvettük az initeket mehetnek a havoc változók
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

    /////////////////////////////////////////////
    // Végigmegyünk az operationökön

    Btor2Circuit.ops.forEach() {
      val loc = nextLoc(false, false, false)

      procBuilder.addLoc(loc)

      val edge = XcfaEdge(lastLoc, loc, StmtLabel(it.value.getStmt()), EmptyMetaData)
      procBuilder.addEdge(edge)
      lastLoc = loc
    }
    procBuilder.createErrorLoc()
    // Error kezelése
    // Egyszerű példáink vannak, tehát egyelőre csak bad van benne
    // Csak egy lesz -> Legyen hiba, ha több a bad
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

    // Circuit folytatása
    // ha nincsen next akkor azt el kell havocolni
    var nexts =
      Btor2Circuit.states.filter { it.value.getVar()?.name?.startsWith("next_") == true }.toList()
    val firstLoc = procBuilder.getLocs().elementAt(1)

    nexts.forEach {
      newLoc = nextLoc(false, false, false)
      procBuilder.addEdge(XcfaEdge(lastLoc, newLoc, StmtLabel(it.second.getStmt()), EmptyMetaData))
      lastLoc = newLoc
    }
    procBuilder.addEdge(XcfaEdge(lastLoc, firstLoc, metadata = EmptyMetaData))
    return xcfaBuilder.build()
  }

  private fun nextLoc(initial: Boolean, final: Boolean, error: Boolean): XcfaLocation {
    val loc = XcfaLocation("l${i}", initial, final, error, EmptyMetaData)
    i++
    return loc
  }
}

class Btor2Pass() : ProcedurePassManager() {
  // No optimization for now c:
}
