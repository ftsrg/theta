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

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.MallocFunctionPass.Companion.ensureMallocVar
import hu.bme.mit.theta.xcfa.passes.MallocFunctionPass.Companion.firstAllocationRetType
import hu.bme.mit.theta.xcfa.passes.MallocFunctionPass.Companion.mallocVar
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Turns `alloca(size)` into an address assignment, like [MallocFunctionPass] does for `malloc`, but
 * places the block in a different residue class of the pointer base space.
 *
 * The target `alloca(target, size)` writes the fresh base into may be a variable (a plain `alloca`,
 * or a stack-allocated struct/array whose value is its base) or a memory cell (a struct's
 * struct/array-typed *field*, whose base lives at `arrays[parent][i]`). The assignment dispatches
 * on which -- an ordinary assign for the variable, a memory-write for the cell -- so that every
 * stack object gets a *fresh runtime* base per allocation. A compile-time constant base would be
 * the same for every activation of the procedure, so two recursive frames or two threads running it
 * would alias; a runtime base from the shared counter cannot.
 *
 * Pointer bases are partitioned by residue mod 3: `3k+0` is malloc'd heap memory, `3k+2` is
 * address-taken locals ([ReferenceElimination]). The memcleanup check
 * ([MemsafetyPass.annotateLost]) scans `3k+0` only, so a block that is *not* the program's
 * responsibility to free must not live there. Memory from `alloca` is released automatically when
 * the enclosing function returns, so reporting it as a leak would be wrong; it therefore gets the
 * free residue class, `3k+1`. It still records a real size in `__theta_ptr_size`, so out-of-bounds
 * accesses to it are caught exactly as they are for heap memory.
 *
 * The shared `__malloc` counter is bumped by 3 for every allocation of either kind, so each
 * allocation consumes its own `k` and no two blocks can alias.
 *
 * Known gaps (both are the pre-existing scope-lifetime limitation, not new to alloca): the block is
 * never invalidated at function return, so a dangling access to it afterwards is not caught, and
 * `free()`ing it is accepted rather than reported as an invalid free.
 *
 * Requires the ProcedureBuilder be `deterministic`.
 */
class AllocaFunctionPass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val mallocVar = builder.parent.mallocVar(parseContext)
    checkNotNull(builder.metaData["deterministic"])
    // Seed the counter before the snapshot below is taken: doing it mid-loop invalidates the
    // snapshot's init-procedure edges (see [ensureMallocVar]).
    builder.firstAllocationRetType(parseContext, this::predicate)?.let {
      builder.parent.ensureMallocVar(parseContext, it)
    }
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::predicate)
      if (
        edges.size > 1 ||
          (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach { e ->
          if (predicate((e.label as SequenceLabel).labels[0])) {
            val invokeLabel = e.label.labels[0] as InvokeLabel
            // The target may be a variable (a bare `alloca`, or a stack struct/array) or a memory
            // cell (a struct/array-typed field). AssignStmtLabel below dispatches on which.
            val ret = invokeLabel.params[0]
            val arg = invokeLabel.params[1]
            val retType = CComplexType.getType(ret, parseContext)
            val bump =
              AssignStmtLabel(
                mallocVar,
                Add(mallocVar.ref, retType.getValue("3")),
                ret.type,
                EmptyMetaData,
              )
            // 3k+1: the residue class the memcleanup scan does not enumerate.
            val assignRet =
              AssignStmtLabel(
                ret,
                cast(
                  FlatMemoryPass.flatBaseExpr(
                    Add(mallocVar.ref, retType.getValue("1")),
                    retType,
                    parseContext,
                  ),
                  ret.type,
                ),
              )
            val labels =
              if (MemsafetyPass.enabled) {
                listOfNotNull(
                  bump,
                  assignRet,
                  builder.parent.allocate(parseContext, ret, arg),
                  probeFirstCell(builder, ret, arg, retType),
                )
              } else {
                listOf(bump, assignRet)
              }
            builder.addEdge(XcfaEdge(e.source, e.target, SequenceLabel(labels), e.metadata))
          } else {
            builder.addEdge(e)
          }
        }
      }
    }
    return builder
  }

  /**
   * Reads the first cell of a *runtime-sized* stack object, so that the existing valid-deref guard
   * sees a zero-length one.
   *
   * C11 6.7.6.2p5: a variably-modified type's size "shall evaluate to a value greater than zero",
   * so `unsigned n = __VERIFIER_nondet_uint(); int a[n];` is undefined for `n == 0`, and
   * sv-benchmarks files that under `valid-deref`. Nothing could see it: with `n == 0` the object is
   * given size 0, every `for (i = 0; i < n; i++)` runs zero times, so **no dereference happens at
   * all** and no access guard can fire. Seven `loops/` tasks -- `sum_array-1`/`-2`, `matrix-2`,
   * `insertion_sort-1`/`-2`, `invert_string-2`, `bubble_sort-1` -- are exactly this shape and
   * nothing else, and theta proved every one of them safe.
   *
   * Stated as a *read of cell 0* rather than as an error edge of its own, because
   * [MemsafetyPass.annotateDeref] already draws precisely the right conclusion from one: its guard
   * is `ptr_size[base] <= index`, which at index 0 is `size <= 0` -- true exactly when the
   * declaration was undefined, and false for every `n >= 1`. Emitting the error edge here instead
   * does not work: [MemsafetyPass.breakUpErrors] runs ten pass-groups later and begins by
   * redirecting *every* incoming edge of the error location to the final location (that is how
   * `reach_error()` is disabled under memsafety), so the check was silently neutralised.
   *
   * Only for a size that is not a literal, so a declared `int a[10]` and the constant-sized
   * subobject allocations cost nothing; and only under memsafety, so no other property sees a read
   * the program never performed.
   */
  private fun probeFirstCell(
    builder: XcfaProcedureBuilder,
    ret: Expr<*>,
    size: Expr<*>,
    retType: CComplexType,
  ): XcfaLabel? {
    if (ExprUtils.simplify(size) is LitExpr<*>) return null
    val element = (retType as? CPointer)?.embeddedType ?: return null
    val probe = Var("__theta_vla_probe_${probeCnt++}", element.smtType)
    builder.addVar(probe)
    parseContext.metadata.create(probe.ref, "cType", element)
    val offset = CComplexType.getUnsignedLong(parseContext).nullValue
    @Suppress("UNCHECKED_CAST")
    val cell =
      Dereference.of(ret as Expr<Type>, offset as Expr<Type>, element.smtType as Type)
    parseContext.metadata.create(cell, "cType", element)
    return AssignStmtLabel(probe, cast(cell, probe.type), probe.type)
  }

  private var probeCnt = 0

  private fun predicate(it: XcfaLabel): Boolean {
    return it is InvokeLabel && it.name == "alloca"
  }
}
