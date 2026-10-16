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
package hu.bme.mit.theta.xcfa.dss.actor

import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.BasicSubstitution
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper
import hu.bme.mit.theta.grammar.dsl.type.TypeWrapper
import hu.bme.mit.theta.xcfa.XcfaScope
import hu.bme.mit.theta.xcfa.dss.analysis.DssAuxVars
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.utils.collectVars
import java.io.DataInputStream
import java.io.DataOutputStream

private const val TRANSPORT_PREFIX = "__dss_transport_"

/**
 * Transfers DSS message expressions between processes as `toString()` text: program variables by
 * name, [DssAuxVars] by `(index, type)`. Round trips are exact unless quantifiers are involved.
 */
class DssExprCodec(private val xcfa: XCFA) {

  private val programVars: Map<String, VarDecl<*>>

  init {
    val byName = xcfa.collectVars().groupBy { it.name }
    val ambiguous = byName.filterValues { it.size > 1 }.keys
    require(ambiguous.isEmpty()) { "Variable names are not unique, cannot transfer: $ambiguous" }
    programVars = byName.mapValues { it.value.single() }
  }

  fun write(out: DataOutputStream, expr: Expr<BoolType>) {
    val aux = mutableListOf<VarDecl<*>>()
    for (decl in ExprUtils.getVars(expr) + ExprUtils.getConstants(expr)) {
      when {
        decl is VarDecl<*> && DssAuxVars.isAux(decl) -> aux += decl
        decl is VarDecl<*> && programVars[decl.name] === decl -> {}
        else ->
          error("Cannot transfer ${decl.name} (${decl.javaClass.simpleName}) to another process")
      }
    }
    val substitution = BasicSubstitution.builder()
    aux.forEachIndexed { i, decl ->
      substitution.put(decl, Var("$TRANSPORT_PREFIX$i", decl.type).ref)
    }
    out.writeInt(aux.size)
    for (decl in aux) {
      out.writeInt(DssAuxVars.indexOf(decl)!!)
      writeString(out, decl.type.toString())
    }
    writeString(out, (if (aux.isEmpty()) expr else substitution.build().apply(expr)).toString())
  }

  @Suppress("UNCHECKED_CAST")
  fun read(input: DataInputStream): Expr<BoolType> {
    val symbols = SymbolTable()
    val env = Env()
    fun define(name: String, decl: Decl<*>) {
      val symbol = Symbol { name }
      symbols.add(symbol)
      env.define(symbol, decl)
    }
    programVars.forEach { (name, decl) -> define(name, decl) }
    repeat(input.readInt()) { i ->
      val index = input.readInt()
      val type = TypeWrapper(readString(input)).instantiate()
      define("$TRANSPORT_PREFIX$i", DssAuxVars.of(index, type))
    }
    return ExpressionWrapper(XcfaScope(symbols), readString(input)).instantiate(env)
      as Expr<BoolType>
  }

  /**
   * The program's locations in a fixed order: names come from a JVM-wide counter, so they differ
   * between processes, but every process that parsed the program builds them in the same order.
   */
  private val locationList: List<XcfaLocation> by lazy { xcfa.procedures.flatMap { it.locs } }
  private val locationIndex: Map<XcfaLocation, Int> by lazy {
    locationList.withIndex().associate { (index, location) -> location to index }
  }

  fun writeLocation(out: DataOutputStream, location: XcfaLocation) {
    out.writeInt(locationIndex[location] ?: error("Not a program location: ${location.name}"))
  }

  fun readLocation(input: DataInputStream): XcfaLocation =
    input.readInt().let { locationList.getOrNull(it) ?: error("Unknown program location #$it") }

  /** An edge as its ends and its position among the parallel edges with the same ends. */
  fun writeEdge(out: DataOutputStream, edge: XcfaEdge) {
    writeLocation(out, edge.source)
    writeLocation(out, edge.target)
    val index = edge.source.outgoingEdges.filter { it.target == edge.target }.indexOf(edge)
    check(index >= 0) { "Not a program edge: $edge" }
    out.writeInt(index)
  }

  fun readEdge(input: DataInputStream): XcfaEdge {
    val source = readLocation(input)
    val target = readLocation(input)
    val index = input.readInt()
    return source.outgoingEdges.filter { it.target == target }.getOrNull(index)
      ?: error("Unknown program edge ${source.name} -> ${target.name} #$index")
  }
}

internal fun writeString(out: DataOutputStream, s: String) {
  val bytes = s.toByteArray(Charsets.UTF_8)
  out.writeInt(bytes.size)
  out.write(bytes)
}

internal fun readString(input: DataInputStream): String {
  val bytes = ByteArray(input.readInt())
  input.readFully(bytes)
  return String(bytes, Charsets.UTF_8)
}
