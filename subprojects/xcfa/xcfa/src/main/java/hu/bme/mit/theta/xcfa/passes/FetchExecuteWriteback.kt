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
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.MemoryAssign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.dereferencesWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isRead
import hu.bme.mit.theta.xcfa.utils.isWritten

/**
 * Transforms derefs into variables if possible (in the entire XCFA, no derefs remain non-literal)
 * Requires the ProcedureBuilder be `deterministic`.
 */
class FetchExecuteWriteback(val parseContext: ParseContext) : ProcedurePass {

  companion object {

    var enabled = false

    private var cnt = 0
      get() = field++
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!enabled) return builder
    checkNotNull(builder.metaData["deterministic"])
    val localDerefs = builder.getEdges().flatMap { it.getFlatLabels().flatMap { it.dereferences } }

    if (localDerefs.isNotEmpty()) {
      val edges = builder.getEdges().filter { it.label.dereferences.isNotEmpty() }.toSet()
      for (edge in edges) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(edge.label.replaceDerefs(builder)))
      }

      return DeterministicPass().run(NormalizePass().run(builder))
    }

    return builder
  }

  private fun XcfaLabel.replaceDerefs(builder: XcfaProcedureBuilder): XcfaLabel =
    if (dereferences.isNotEmpty()) {
      when (this) {
        is NondetLabel -> NondetLabel(labels.map { it.replaceDerefs(builder) }.toSet(), metadata)
        is SequenceLabel -> SequenceLabel(labels.map { it.replaceDerefs(builder) }, metadata)
        is InvokeLabel -> {
          val lut = getDerefLut(dereferences, builder)
          SequenceLabel(
            lut.map {
              StmtLabel(
                Assign(
                  cast(it.value, it.value.type),
                  cast(it.key.map { it.replaceDerefs(lut) }, it.value.type),
                )
              )
            } +
              InvokeLabel(
                this.name,
                this.params.map { it.replaceDerefs(lut) },
                metadata,
                tempLookup,
                isLibraryFunction,
              ),
            metadata,
          )
        }

        is StartLabel -> {
          val lut = getDerefLut(dereferences, builder)
          SequenceLabel(
            lut.map {
              StmtLabel(
                Assign(
                  cast(it.value, it.value.type),
                  cast(it.key.map { it.replaceDerefs(lut) }, it.value.type),
                )
              )
            } +
              StartLabel(name, params.map { it.replaceDerefs(lut) }, pidVar, metadata, tempLookup),
            metadata,
          )
        }

        is StmtLabel ->
          SequenceLabel(
            stmt.replaceDerefs(builder).map { StmtLabel(it, choiceType, metadata) },
            metadata,
          )

        else -> error("Not implemented for ${this.javaClass.simpleName}")
      }
    } else this

  private fun getDerefLut(dereferences: List<Dereference<*, *, *>>, builder: XcfaProcedureBuilder) =
    dereferences.associateWith {
      val tmpVar = Var("__THETA_heap_tmp_$cnt", it.type)
      builder.addVar(tmpVar)
      tmpVar
    }

  private fun Stmt.replaceDerefs(builder: XcfaProcedureBuilder): List<Stmt> {
    val lut = getDerefLut(dereferences, builder)
    val stmt: Stmt =
      when (this) {
        is MemoryAssignStmt<*, *, *> ->
          if (this.deref in lut)
            Assign(cast(lut[deref], expr.type), cast(expr.replaceDerefs(lut), expr.type))
          else {
            MemoryAssign(
              deref.map { it.replaceDerefs(lut) } as Dereference<*, *, Type>,
              cast(expr.replaceDerefs(lut), expr.type),
            )
          }

        is AssignStmt<*> ->
          AssignStmt.of(cast(varDecl, varDecl.type), cast(expr.replaceDerefs(lut), varDecl.type))
        is AssumeStmt -> AssumeStmt.of(cond.replaceDerefs(lut) as Expr<BoolType>)
        else -> this
      }
    val ret = ArrayList<Stmt>()
    val accessType = dereferencesWithAccessType.filter { it.key in dereferences }
    for (dereference in accessType.filter { it.value.isRead }.map { it.key }) {
      ret.add(
        Assign(
          cast(lut[dereference]!!, dereference.type),
          cast(
            dereference.map { it.replaceDerefs(lut.filter { it.key != dereference }) },
            dereference.type,
          ),
        )
      )
    }
    ret.add(stmt)
    for (dereference in accessType.filter { it.value.isWritten }.map { it.key }) {
      ret.add(
        MemoryAssign(
          cast(
            dereference.map { it.replaceDerefs(lut.filter { it.key != dereference }) },
            dereference.type,
          )
            as Dereference<*, *, Type>,
          cast(lut[dereference]!!, dereference.type).ref,
        )
      )
    }
    return ret
  }

  private fun Expr<*>.replaceDerefs(lut: Map<Dereference<*, *, *>, VarDecl<*>>): Expr<*> =
    if (this in lut) {
      lut[this]!!.ref
    } else {
      withOps(ops.map { it.replaceDerefs(lut) })
    }
}
