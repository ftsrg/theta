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
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.xcfa.model.*
import java.math.BigInteger

/**
 * Replaces calls to unresolved external functions (neither a procedure defined in the XCFA nor
 * handled by an earlier pass such as [CLibraryFunctionsPass], [MallocFunctionPass] or
 * [NondetFunctionPass]) with a havoc of their return value -- but ONLY when this cannot silently
 * change the verdict:
 * - the callee must not be flagged [InvokeLabel.isLibraryFunction] (those are handled at analysis
 *   time),
 * - the callee must not be a control-flow function (setjmp/longjmp family),
 * - the return value must be a plain integer scalar (or void): havocing a returned pointer produces
 *   arbitrary-base dereferences downstream, and float-returning math functions (ceil, sin, ...)
 *   have value semantics that a havoc misrepresents in both verdict directions,
 * - every argument must be a plain integer scalar or a literal null pointer: a pointer argument may
 *   be written through by the callee (fscanf(_, _, &data)!), and swallowing that write makes the
 *   model deterministic where the program is not -- proven "safe" vacuously.
 *
 * Calls that do not satisfy these conditions are left untouched; they then fail the analysis with
 * "No such method X" and the portfolio moves on -- an error result, which is always preferable to a
 * wrong verdict.
 *
 * This must run after [InlineProceduresPass]/[NondetFunctionPass], so that genuine (including
 * recursive) procedures and modeled library functions are already gone.
 */
class UnresolvedInvokeToHavocPass(
  private val parseContext: ParseContext,
  private val uniqueWarningLogger: Logger,
) : ProcedurePass {

  companion object {
    /** Functions with control-flow semantics that must never be modeled as a havoc. */
    private val CONTROL_FLOW_FUNCTIONS =
      setOf("setjmp", "_setjmp", "sigsetjmp", "__sigsetjmp", "longjmp", "siglongjmp", "_longjmp")
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val definedProcedures = builder.parent.getProcedures().map { it.name }.toSet()
    val pred: (XcfaLabel) -> Boolean = {
      it is InvokeLabel &&
        !it.isLibraryFunction &&
        it.name !in definedProcedures &&
        it.name !in CONTROL_FLOW_FUNCTIONS &&
        isHavocSafe(it)
    }

    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(pred)
      if (
        edges.size > 1 || (edges.size == 1 && pred((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          if (pred((it.label as SequenceLabel).labels[0])) {
            val invokeLabel = it.label.labels[0] as InvokeLabel
            uniqueWarningLogger.write(
              Logger.Level.INFO,
              "WARNING: call to unresolved function %s is modeled as a havoc of its return value;" +
                " any side effects (e.g. writes to globals) are swallowed.\n",
              invokeLabel.name,
            )
            val returnSlot = invokeLabel.params[0] as RefExpr<*>
            val havoc = HavocStmt.of(returnSlot.decl as VarDecl<*>)
            builder.addEdge(
              XcfaEdge(
                it.source,
                it.target,
                SequenceLabel(
                  listOf(StmtLabel(havoc, metadata = invokeLabel.metadata)) +
                    withinTypeRange(returnSlot, parseContext, invokeLabel.metadata)
                ),
                it.metadata,
              )
            )
          } else {
            builder.addEdge(it)
          }
        }
      }
    }
    return builder
  }

  /**
   * True iff havocing the return value of this call cannot silently misrepresent the callee:
   * integer-scalar (or void) return, and each argument integer-scalar or literal null.
   */
  private fun isHavocSafe(invokeLabel: InvokeLabel): Boolean {
    if (invokeLabel.params.isEmpty()) return false
    val returnSlot = invokeLabel.params[0]
    if (returnSlot !is RefExpr<*> || returnSlot.decl !is VarDecl<*>) return false
    val returnType = cTypeOf(returnSlot) ?: return false
    if (!(returnType is CVoid || isPlainIntegerScalar(returnType))) return false
    return invokeLabel.params.drop(1).all { arg ->
      if (isNullLiteral(arg)) true
      else {
        val argType = cTypeOf(arg)
        argType != null && isPlainIntegerScalar(argType)
      }
    }
  }

  /**
   * The frontend-recorded C type of the expression, or null when unknown. Deliberately avoids
   * [CComplexType.getType]'s SMT-type fallback: under integer arithmetic a pointer is an
   * integer-typed expression, so the fallback would misreport pointers as scalars.
   */
  private fun cTypeOf(expr: Expr<*>): CComplexType? {
    val meta = parseContext.metadata.getMetadataValue(expr, "cType")
    if (meta.isEmpty) return null
    return when (val value = meta.get()) {
      is CComplexType -> value
      else -> null
    }
  }

  private fun isPlainIntegerScalar(type: CComplexType): Boolean =
    type is CInteger && type !is CPointer && type !is CArray

  /**
   * A literal null pointer (integer or bitvector zero) cannot be written through. Constant-folds
   * first: pointer casts wrap literals in modulo arithmetic, e.g. `(void*)0` arrives as `(mod (mod
   * 0 2^64) 2^64)`.
   */
  private fun isNullLiteral(expr: Expr<*>): Boolean =
    when (val folded = ExprUtils.simplify(expr)) {
      is IntLitExpr -> folded.value == BigInteger.ZERO
      is BvLitExpr -> folded.value.all { !it }
      else -> false
    }
}
