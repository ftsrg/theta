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

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.declaration.FunctionIds
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Expands a call through a function pointer into a nondeterministic dispatch over its candidate
 * set.
 *
 * The frontend emits such a call as a marker [InvokeLabel] named [INDIRECT_CALL] whose parameters
 * are `[returnValue, functionPointer, actualArgs...]`. This pass replaces it with a [NondetLabel]
 * offering one branch per candidate function:
 * ```
 *   assume(fp == id(f));  ret := f(args...)
 * ```
 *
 * plus a final branch `assume(fp != id(f) for every candidate f); havoc ret`, which keeps the model
 * total (a pointer that matches no candidate -- e.g. NULL -- would be undefined behavior in C).
 *
 * The candidate set is the set of functions whose address is taken anywhere in the program (see
 * [FunctionIds]), restricted to those actually defined in this XCFA with a matching arity. This
 * must run before [InlineProceduresPass] so that the direct calls it emits are inlined normally.
 *
 * Programs that never call through a function pointer contain no marker call and are left
 * bit-for-bit unchanged.
 */
class FunctionPointerCallsPass(
  private val parseContext: ParseContext,
  private val uniqueWarningLogger: Logger,
) : ProcedurePass {

  companion object {
    /** Must match `ExpressionVisitor.INDIRECT_CALL`. */
    const val INDIRECT_CALL = "__theta_indirect_call"
  }

  private fun isIndirectCall(label: XcfaLabel) = label is InvokeLabel && label.name == INDIRECT_CALL

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    // Fast path: programs without indirect calls are not touched at all.
    if (builder.getEdges().none { edge -> edge.getFlatLabels().any(::isIndirectCall) }) {
      return builder
    }
    checkNotNull(builder.metaData["deterministic"])

    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(::isIndirectCall)
      if (
        edges.size > 1 ||
          (edges.size == 1 && isIndirectCall((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          if (isIndirectCall((it.label as SequenceLabel).labels[0])) {
            val invokeLabel = it.label.labels[0] as InvokeLabel
            // One parallel edge per candidate: the nondeterministic choice between them IS the
            // dispatch. Each branch keeps its call at the top level of a SequenceLabel so that
            // InlineProceduresPass can inline it normally.
            dispatchBranches(builder, invokeLabel).forEach { branch ->
              builder.addEdge(XcfaEdge(it.source, it.target, branch, it.metadata))
            }
          } else {
            builder.addEdge(it)
          }
        }
      }
    }
    return builder
  }

  private fun dispatchBranches(
    builder: XcfaProcedureBuilder,
    invokeLabel: InvokeLabel,
  ): List<SequenceLabel> {
    val returnValue = invokeLabel.params[0]
    val functionPointer = invokeLabel.params[1]
    val arguments = invokeLabel.params.drop(2)

    val pointerType = CComplexType.getType(functionPointer, parseContext)
    val candidates =
      FunctionIds.getAll()
        .filter { (name, _) ->
          builder.parent.getProcedures().any { proc ->
            proc.name == name && proc.getParams().size == arguments.size + 1
          }
        }
        .map { (name, id) ->
          Pair(name, AbstractExprs.Eq(functionPointer, pointerType.getValue(id.toString())))
        }

    if (candidates.isEmpty()) {
      uniqueWarningLogger.write(
        Logger.Level.INFO,
        "WARNING: call through a function pointer with no candidate function of matching arity;" +
          " modeling it as a havoc of the return value.\n",
      )
      return listOf(SequenceLabel(listOf(havocReturnValue(returnValue, invokeLabel))))
    }

    val branches =
      candidates
        .map { (name, guard) ->
          SequenceLabel(
            listOf(
              StmtLabel(AssumeStmt.of(guard), metadata = invokeLabel.metadata),
              InvokeLabel(
                name,
                listOf(returnValue) + arguments,
                metadata = invokeLabel.metadata,
                tempLookup = invokeLabel.tempLookup,
              ),
            )
          )
        }
        .toMutableList()

    // A pointer matching no candidate (e.g. NULL) is undefined behavior in C; keep the model total
    // by allowing any return value rather than silently pruning the path.
    branches.add(
      SequenceLabel(
        listOf(
          StmtLabel(
            AssumeStmt.of(And(candidates.map { (_, guard) -> Not(guard) })),
            metadata = invokeLabel.metadata,
          ),
          havocReturnValue(returnValue, invokeLabel),
        )
      )
    )
    return branches
  }

  private fun havocReturnValue(returnValue: Expr<*>, invokeLabel: InvokeLabel): XcfaLabel =
    StmtLabel(
      HavocStmt.of((returnValue as RefExpr<*>).decl as VarDecl<*>),
      metadata = invokeLabel.metadata,
    )
}
