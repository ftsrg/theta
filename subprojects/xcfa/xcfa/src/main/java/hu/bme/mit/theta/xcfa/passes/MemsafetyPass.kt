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
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall
import hu.bme.mit.theta.xcfa.dereferences
import hu.bme.mit.theta.xcfa.model.*

/**
 * Adds assumptions to the XCFA if memory safety needs to be checked. Rules based on:
 * https://sv-comp.sosy-lab.org/2025/rules.php Summary:
 * - valid-free: All memory deallocations are valid (counterexample: invalid free). More precisely:
 *   There exists no finite execution of the program on which an invalid memory deallocation occurs.
 *     - inserted check: at every free, we check if pointer is valid (no NULLPTR, no double free).
 * - valid-deref: All pointer dereferences are valid (counterexample: invalid dereference). More
 *   precisely: There exists no finite execution of the program on which an invalid pointer
 *   dereference occurs.
 *     - inserted check: at every dereference, we check if pointer is valid (non-null, non-freed,
 *       in-size)
 * - valid-memtrack: All allocated memory is tracked, i.e., pointed to or deallocated
 *   (counterexample: memory leak). More precisely: There exists no finite execution of the program
 *   on which the program lost track of some previously allocated memory. (Comparison to Valgrind:
 *   This property is violated if Valgrind reports 'definitely lost'.)
 *     - inserted check: we keep track of variables.
 */
class MemsafetyPass(val parseContext: ParseContext) : ProcedurePass {

  companion object {
    var NEED_CHECK = false
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!NEED_CHECK) return builder

    breakUpErrors(builder)

    annotateFree(builder)

    annotateDeref(builder)

    annotateLost(builder)

    return builder
  }

  private val pointerType = CPointer(null, null, parseContext)
  val fitsall = Fitsall(null, parseContext)

  private fun breakUpErrors(builder: XcfaProcedureBuilder) {
    val errorLoc =
      builder.errorLoc.orElseGet { builder.createErrorLoc().let { builder.errorLoc.get() } }
    val finalLoc =
      builder.finalLoc.orElseGet { builder.createFinalLoc().let { builder.finalLoc.get() } }

    LinkedHashSet(errorLoc.incomingEdges).forEach {
      builder.removeEdge(it)
      builder.addEdge(it.withTarget(finalLoc))
    }
  }

  private fun annotateFree(builder: XcfaProcedureBuilder) {
    val errorLoc =
      builder.errorLoc.orElseGet { builder.createErrorLoc().let { builder.errorLoc.get() } }

    val invalidFree = XcfaLocation("__THETA_bad_free", metadata = EmptyMetaData)
    builder.addLoc(invalidFree)
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::free)
      if (
        edges.size > 1 || (edges.size == 1 && free((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          if (free((it.label as SequenceLabel).labels[0])) {
            val invokeLabel = it.label.labels[0] as InvokeLabel
            val argument = invokeLabel.params[1]
            val sizeVar = builder.parent.getPtrSizeVar()
            val derefAssume =
              Assume(
                Or(
                  Leq(argument, pointerType.nullValue), // uninit ptr
                  // freed/not big enough ptr
                  Leq(
                    ArrayReadExpr.create<Type, Type>(sizeVar.ref, argument),
                    pointerType.nullValue,
                  ), // freed/not big enough ptr
                )
              )

            builder.addEdge(
              XcfaEdge(
                it.source,
                it.target,
                SequenceLabel(
                  listOf(builder.parent.allocate(parseContext, argument, fitsall.nullValue))
                ),
                it.metadata,
              )
            )
            builder.addEdge(
              XcfaEdge(
                it.source,
                invalidFree,
                SequenceLabel(listOf(StmtLabel(derefAssume))),
                it.metadata,
              )
            )
            builder.addEdge(
              XcfaEdge(invalidFree, errorLoc, SequenceLabel(listOf(NopLabel)), it.metadata)
            )
          } else {
            builder.addEdge(it)
          }
        }
      }
    }
  }

  private fun annotateDeref(builder: XcfaProcedureBuilder) {
    val errorLoc =
      builder.errorLoc.orElseGet { builder.createErrorLoc().let { builder.errorLoc.get() } }
    val badDeref = XcfaLocation("__THETA_bad_deref", metadata = EmptyMetaData)
    builder.addLoc(badDeref)
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::deref)
      if (
        edges.size > 1 || (edges.size == 1 && deref((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          if (
            deref((it.label as SequenceLabel).labels[0])
          ) { // if dereference is in a short-circuiting path, add prior assumptions as well.
            val derefAssume =
              Assume(
                Or(
                  Or(
                    it.label.labels[0].dereferences.map { Leq(it.array, pointerType.nullValue) }
                  ), // uninit ptr
                  Or(
                    it.label.labels[0].dereferences.map {
                      val sizeVar = builder.parent.getPtrSizeVar()
                      Leq(
                        ArrayReadExpr.create<Type, Type>(sizeVar.ref, it.array),
                        it.offset,
                      ) // freed/not big enough ptr
                    }
                  ),
                  Or(
                    it.label.labels[0].dereferences.map {
                      Lt(it.offset, fitsall.nullValue) // negative index
                    }
                  ),
                )
              )
            builder.addEdge(it)
            builder.addEdge(
              XcfaEdge(
                it.source,
                badDeref,
                SequenceLabel(
                  listOf(StmtLabel(derefAssume))
                ), // deref(x a), x <= 0 || a >= sizeof(x)
                it.metadata,
              )
            )
            builder.addEdge(
              XcfaEdge(badDeref, errorLoc, SequenceLabel(listOf(NopLabel)), it.metadata)
            )
          } else {
            builder.addEdge(it)
          }
        }
      }
    }
  }

  fun annotateLost(builder: XcfaProcedureBuilder) {
    val errorLoc =
      builder.errorLoc.orElseGet { builder.createErrorLoc().let { builder.errorLoc.get() } }
    val finalLoc =
      builder.finalLoc.orElseGet { builder.createFinalLoc().let { builder.finalLoc.get() } }
    val lostLoc = XcfaLocation("__THETA_lost", metadata = EmptyMetaData)
    builder.addLoc(lostLoc)

    val sizeVar = builder.parent.getPtrSizeVar()
    val anyBase =
      builder.parent.getVars().find { it.wrappedVar.name == "__ptr" }?.wrappedVar
        ?: XcfaGlobalVar(Var("__ptr", sizeVar.type.indexType), pointerType.nullValue)
          .also { builder.parent.addVar(it) }
          .wrappedVar
    val remained = // 3k+0: malloc
      Gt(
        ArrayReadExpr.create<Type, Type>(sizeVar.ref, Mul(anyBase.ref, pointerType.getValue("3"))),
        fitsall.nullValue,
      )

    for (incomingEdge in LinkedHashSet(finalLoc.incomingEdges)) {
      builder.removeEdge(incomingEdge)
      val newLoc = XcfaLocation("pre-final", metadata = EmptyMetaData)
      builder.addLoc(newLoc)
      builder.addEdge(incomingEdge.withTarget(newLoc))
      builder.addEdge(
        XcfaEdge(
          newLoc,
          lostLoc,
          label = SequenceLabel(listOf(StmtLabel(Assume(remained)))),
          metadata = EmptyMetaData,
        )
      )
      builder.addEdge(
        XcfaEdge(
          lostLoc,
          errorLoc,
          label = SequenceLabel(listOf(NopLabel)),
          metadata = EmptyMetaData,
        )
      )
    }
  }

  private fun free(it: XcfaLabel): Boolean {
    return it is InvokeLabel && it.name == "free"
  }

  private fun deref(it: XcfaLabel): Boolean {
    return it.dereferences.isNotEmpty()
  }
}
