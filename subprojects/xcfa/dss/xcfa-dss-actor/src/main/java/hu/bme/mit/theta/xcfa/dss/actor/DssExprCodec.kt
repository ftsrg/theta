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
import hu.bme.mit.theta.xcfa.utils.collectVars
import java.io.DataInputStream
import java.io.DataOutputStream

private const val TRANSPORT_PREFIX = "__dss_transport_"

/**
 * Transfers DSS message expressions between processes as `toString()` text: program variables by
 * name, [DssAuxVars] by `(index, type)`. Round trips are exact unless quantifiers are involved.
 */
class DssExprCodec(xcfa: XCFA) {

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
