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

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.references
import java.math.BigInteger

class ReferenceDereferenceSimplifier(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {

    val withOffset = mutableMapOf<Pair<VarDecl<*>, BigInteger>, VarDecl<*>>()
    fun VarDecl<*>.withOffset(offset: BigInteger): VarDecl<*> =
      withOffset.computeIfAbsent(this to offset) {
        val newVar = Var(name + "_offset$offset", type)
        if (builder.getVars().contains(this)) {
          builder.addVar(newVar)
        } else if (builder.parent.getVars().any { it.wrappedVar == this }) {
          val oldVar = builder.parent.getVars().first { it.wrappedVar == this }
          builder.parent.addVar(oldVar.copy(wrappedVar = newVar))
        }
        newVar
      }

    val references =
      builder.getEdges().flatMap {
        it.getFlatLabels().flatMap { it.references.filter { it.expr is Dereference<*, *, *> } }
      }
    if (references.isEmpty()) {
      return builder
    }

    val lut =
      references
        .mapNotNull {
          val deref = (it.expr as Dereference<*, *, *>)
          val offset = deref.offset
          val array = deref.array
          if (offset is LitExpr<*>) {
            val offsetValue =
              when (offset.type) {
                is IntType -> (offset as IntLitExpr).value
                is BvType -> BvUtils.neutralBvLitExprToBigInteger(offset as BvLitExpr)
                else -> error("Unsupported offset type ${offset.type}")
              }
            if (offsetValue.equals(BigInteger.ZERO)) {
              it to array
            } else if (array is RefExpr<*>) {
              it to (array.decl as VarDecl).withOffset(offsetValue).ref
            } else {
              null
            }
          } else {
            null
          }
        }
        .toMap<Expr<*>, Expr<*>>()

    for (edge in builder.getEdges().toSet()) {
      edge.label is SequenceLabel
      val oldLabels = edge.label.getFlatLabels()
      val newLabels = oldLabels.map { label -> label.changeSubexpr(lut, parseContext) }
      if (oldLabels != newLabels) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(newLabels, metadata = edge.label.metadata)))
      }
    }

    return builder
  }
}
