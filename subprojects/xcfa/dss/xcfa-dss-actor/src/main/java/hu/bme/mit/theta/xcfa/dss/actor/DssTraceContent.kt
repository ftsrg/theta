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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.FalseExpr
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.booltype.ImplyExpr
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.booltype.QuantifiedExpr
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import hu.bme.mit.theta.core.type.booltype.XorExpr
import hu.bme.mit.theta.xcfa.dss.analysis.DssAuxVars
import java.util.IdentityHashMap

/**
 * Trace fields describing a condition's content: `disj`, `nodes`, `atoms`, `vars`, `aux` (see
 * [DssAuxVars]) and `top`; with [DssTrace.expressions], the formula itself as a final `expr` field.
 */
internal fun traceContent(expr: Expr<BoolType>?): Array<Pair<String, Any?>> {
  if (expr == null) return arrayOf("disj" to 0, "stub" to true)
  val visited = IdentityHashMap<Expr<*>, Unit>()
  val atoms = HashSet<Expr<*>>()
  val vars = HashSet<VarDecl<*>>()
  fun visit(e: Expr<*>) {
    if (visited.put(e, Unit) != null) return
    if (e is RefExpr<*>) (e.decl as? VarDecl<*>)?.let { vars += it }
    e.ops.forEach(::visit)
  }
  val seen = IdentityHashMap<Expr<*>, Unit>()
  fun collectAtoms(e: Expr<*>) {
    if (seen.put(e, Unit) != null) return
    when (e) {
      is AndExpr,
      is OrExpr,
      is NotExpr,
      is ImplyExpr,
      is IffExpr,
      is XorExpr,
      is QuantifiedExpr -> e.ops.forEach(::collectAtoms)
      is BoolLitExpr -> {}
      else -> atoms += e
    }
  }
  visit(expr)
  collectAtoms(expr)
  val aux = vars.count(DssAuxVars::isAux)
  val disj =
    when (expr) {
      is FalseExpr -> 0
      is OrExpr -> expr.ops.size
      else -> 1
    }
  val fields =
    arrayOf<Pair<String, Any?>>(
      "disj" to disj,
      "nodes" to visited.size,
      "atoms" to atoms.size,
      "vars" to vars.size - aux,
      "aux" to aux,
      "top" to (expr is TrueExpr),
    )
  return if (DssTrace.expressions) fields + ("expr" to oneLine(expr.toString())) else fields
}

/** Theta's `toString` pretty-prints long formulas over several indented lines. */
private fun oneLine(text: String): String = text.replace(Regex("\\s*\\n\\s*"), " ")
