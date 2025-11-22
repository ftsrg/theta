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
package hu.bme.mit.theta.xcfa.cli.witnesstransformation

import com.google.common.collect.Lists
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.c2xcfa.getCMetaData
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.fptype.FpLitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getXcfaErrorDetector
import hu.bme.mit.theta.xcfa.model.ChoiceType
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.witnesses.WitnessEdge
import hu.bme.mit.theta.xcfa.witnesses.WitnessNode
import java.math.BigInteger
import java.util.function.Predicate

enum class Verbosity {
  NECESSARY,
  SOURCE_EXISTS,
  STMT_EXISTS,
  EVERYTHING,
}

fun traceToWitness(
  verbosity: Verbosity = Verbosity.SOURCE_EXISTS,
  trace: Trace<XcfaState<ExplState>, XcfaAction>,
  parseContext: ParseContext,
  property: XcfaProperty,
): Trace<WitnessNode, WitnessEdge> {
  val newStates = ArrayList<WitnessNode>()
  val newActions = ArrayList<WitnessEdge>()

  val isError =
    if (property.verifiedProperty == ErrorDetection.TERMINATION) {
      Predicate<XcfaState<out PtrState<out ExprState>>> { false }
    } else getXcfaErrorDetector(property.verifiedProperty)

  var lastNode: WitnessNode? = null

  for (i in 0 until trace.length() + 1) {
    val state = trace.states[i]
    val action = trace.actions.getOrNull(i - 1)
    val node =
      WitnessNode(
        id = "N${newStates.size}",
        entry = false,
        sink = false,
        violation =
          isError.test( // this is a hack so that a simple explstate can become a ptrstate
            XcfaState(
              state.xcfa,
              state.processes,
              PtrState(state.sGlobal),
              state.mutexes,
              state.threadLookup,
              state.bottom,
            )
          ),
        xcfaLocations = state.processes.map { Pair(it.key, it.value.locs) }.toMap(),
        cSources =
          state.processes
            .map {
              Pair(it.key, it.value.locs.map { it.getCMetaData()?.sourceText ?: "<unknown>" })
            }
            .toMap(),
        globalState = state.sGlobal,
        // localState = //state
      )
    if (node != WitnessNode(id = "N${newStates.size}")) {
      newStates.add(node)
      if (lastNode != null && action != null) {
        val edge =
          labelToEdge(
            lastNode,
            node,
            action.edge.label,
            action.pid,
            ImmutableValuation.empty(),
            parseContext,
            action.edge,
          )
        newActions.add(edge)
      }
      lastNode = node
    }
  }

  return Trace.of(newStates, newActions)
}

fun targetToWitness(startline: Int, endline: Int, startoffset: Int, endoffset: Int): String {
  return """
  <node id="N0">
  <data key="violation">false</data>
  </node>
  <node id="N1">
  <data key="violation">true</data>
  </node>
  
  <edge source="N0" target="N1">
    <data key="startline">$startline</data>
    <data key="endline">$endline</data>
    <data key="startoffset">$startoffset</data>
    <data key="endoffset">$endoffset</data>
  </edge>
  """
}

fun shouldInclude(edge: WitnessEdge, verbosity: Verbosity): Boolean =
  when (verbosity) {
    Verbosity.NECESSARY ->
      edge.control != null || edge.assumption != null || edge.createThread != null
    Verbosity.SOURCE_EXISTS -> shouldInclude(edge, Verbosity.NECESSARY) || edge.cSource != null
    Verbosity.STMT_EXISTS -> shouldInclude(edge, Verbosity.NECESSARY) || edge.stmt != null
    Verbosity.EVERYTHING -> true
  }

private fun labelToEdge(
  lastNode: WitnessNode,
  node: WitnessNode,
  xcfaLabel: XcfaLabel,
  pid: Int,
  valuation: Valuation,
  parseContext: ParseContext,
  edge: XcfaEdge,
): WitnessEdge {
  return WitnessEdge(
    source = lastNode,
    target = node,
    assumption =
      if (xcfaLabel is StmtLabel && xcfaLabel.stmt is HavocStmt<*>) {
        val varDecl = (xcfaLabel.stmt as HavocStmt<*>).varDecl
        val eval = valuation.eval(varDecl)
        val splitName = varDecl.name.split("::")
        val rootName =
          if (splitName[0].matches(Regex("T[0-9]*")))
            splitName.subList(2, splitName.size).joinToString("::")
          else varDecl.name
        if (parseContext.metadata.getMetadataValue(rootName, "cName").isPresent && eval.isPresent)
          "${parseContext.metadata.getMetadataValue(rootName, "cName").get()} == ${
                    printLit(eval.get())
                }"
        else null
      } else null,
    control =
      if (xcfaLabel is StmtLabel && xcfaLabel.choiceType != ChoiceType.NONE) {
        xcfaLabel.choiceType == ChoiceType.MAIN_PATH
      } else null,
    startline = xcfaLabel.getCMetaData()?.lineNumberStart,
    endline = xcfaLabel.getCMetaData()?.lineNumberStop,
    startoffset = xcfaLabel.getCMetaData()?.offsetStart,
    endoffset = xcfaLabel.getCMetaData()?.offsetEnd,
    startcol = xcfaLabel.getCMetaData()?.colNumberStart,
    endcol = xcfaLabel.getCMetaData()?.colNumberStop,
    threadId = if (pid != null) "$pid" else null,
    stmt = if (xcfaLabel is StmtLabel) xcfaLabel.stmt.toString() else null,
    cSource = xcfaLabel.getCMetaData()?.sourceText,
    edge = edge,
  )
}

fun printLit(litExpr: LitExpr<*>): String? {
  return if (litExpr is BvLitExpr) {
    val value = litExpr.value
    var intValue = BigInteger.ZERO
    for (i in value.indices) {
      val b = value[i]
      if (b) {
        intValue = intValue.add(BigInteger.ONE.shiftLeft(value.size - 1 - i))
      }
    }
    "0x" + intValue.toString(16)
  } else if (litExpr is FpLitExpr) {
    val boolList: MutableList<Boolean> = java.util.ArrayList()
    val tmpList: MutableList<Boolean> = java.util.ArrayList()
    for (b in litExpr.significand.value) {
      tmpList.add(b)
    }
    boolList.addAll(Lists.reverse(tmpList))
    tmpList.clear()
    for (b in litExpr.exponent.value) {
      tmpList.add(b)
    }
    boolList.addAll(Lists.reverse(tmpList))
    boolList.add(litExpr.hidden)
    var aggregate = 0
    val hexDigits: MutableList<Char> = java.util.ArrayList()
    for (i in boolList.indices) {
      if (i % 4 == 0 && i > 0) {
        if (aggregate < 10) hexDigits.add(('0'.code + aggregate).toChar())
        else hexDigits.add(('A'.code - 10 + aggregate).toChar())
        aggregate = 0
      }
      if (boolList[i]) aggregate += 1 shl i % 4
    }
    if (aggregate < 10) hexDigits.add(('0'.code + aggregate).toChar())
    else hexDigits.add(('A'.code - 10 + aggregate).toChar())
    val stringBuilder = StringBuilder("0x")
    for (character in Lists.reverse(hexDigits)) {
      stringBuilder.append(character)
    }
    stringBuilder.toString()
  } else {
    litExpr.toString()
  }
}
