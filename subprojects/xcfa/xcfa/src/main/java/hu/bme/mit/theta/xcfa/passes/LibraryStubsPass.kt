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
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Standard-library functions that nothing defines and [UnresolvedInvokeToHavocPass] refuses.
 *
 * That pass only havocs a call whose arguments are all plain integer scalars, because havocing the
 * return of a function that takes a POINTER would silently swallow whatever it writes through it.
 * The rule is right, but it leaves the entire stdio and string family unmodelled, and such a call
 * reaches the analysis as a procedure that does not exist -- "No such method fscanf" and friends,
 * the single largest source of sub-configuration failure in the run-93 portfolio (`memset` 213,795
 * log occurrences, `fscanf` 211,366, `fgets` 125,945).
 *
 * These are stubbed explicitly instead. Each entry states which arguments the function WRITES
 * THROUGH, and those pointees are filled with fresh nondeterministic values rather than being left
 * at their old contents -- leaving them would be a specific wrong value, which can hide a bug as
 * easily as invent one, where unconstrained is a safe over-approximation.
 *
 * ⚠️ Not modelled here, deliberately: `setjmp`/`longjmp` (non-local control flow -- a havoc would
 * be a wrong program, and [UnresolvedInvokeToHavocPass] already refuses them by name) and the math
 * functions (`sin`, `expf`, ...), whose *values* matter to the programs that call them; a havoc
 * there would turn a precise computation into noise and answer float tasks by accident.
 */
class LibraryStubsPass(val parseContext: ParseContext, val uniqueWarningLogger: Logger) :
  ProcedurePass {

  companion object {
    /**
     * name -> indices into `InvokeLabel.params` that the call writes through.
     *
     * `params[0]` is the return slot, so the C arguments start at 1. An empty set means the call
     * only produces a return value; the whole entry means "this name is a known library function
     * that may be stubbed even though it takes pointers".
     */
    private val STUBS: Map<String, Set<Int>> =
      mapOf(
        // stdio: reads produce nondeterministic data in the caller's buffer
        "fgets" to setOf(1),
        "fscanf" to setOf(3, 4, 5, 6), // (ret, stream, fmt, &a, &b, ...)
        "scanf" to setOf(2, 3, 4, 5),
        "__isoc99_fscanf" to setOf(3, 4, 5, 6),
        "__isoc99_scanf" to setOf(2, 3, 4, 5),
        "read" to setOf(2),
        "fread" to setOf(1),
        "getline" to setOf(1, 2),
        // stdio: writes go to a stream we do not model, so only the return matters
        "fopen" to setOf(),
        "fclose" to setOf(),
        "fflush" to setOf(),
        "fprintf" to setOf(),
        "printf" to setOf(),
        "puts" to setOf(),
        "fputs" to setOf(),
        "fputc" to setOf(),
        "putchar" to setOf(),
        "perror" to setOf(),
        "fwrite" to setOf(),
        // formatting into a caller buffer
        "sprintf" to setOf(1),
        "snprintf" to setOf(1),
        "vsnprintf" to setOf(1),
        "vasprintf" to setOf(1),
        "asprintf" to setOf(1),
        // string/memory inspection -- these only READ, so the return is the whole effect
        "strlen" to setOf(),
        "strnlen" to setOf(),
        "strcmp" to setOf(),
        "strncmp" to setOf(),
        "strcasecmp" to setOf(),
        "memcmp" to setOf(),
        "strchr" to setOf(),
        "strrchr" to setOf(),
        "strstr" to setOf(),
        "strspn" to setOf(),
        "strcspn" to setOf(),
        "strpbrk" to setOf(),
        // process/thread bookkeeping with no memory effect we model
        "atexit" to setOf(),
        "on_exit" to setOf(),
        "at_quick_exit" to setOf(),
        "pthread_key_create" to setOf(1),
        "pthread_key_delete" to setOf(),
        "pthread_setspecific" to setOf(),
        "pthread_getspecific" to setOf(),
      )

    /** How many cells of a written pointee to fill when its extent is not otherwise known. */
    private const val DEFAULT_FILL_CELLS = 1
  }

  private var counter = 0

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val defined = builder.parent.getProcedures().mapNotNull { it.name }.toSet()
    for (edge in ArrayList(builder.getEdges())) {
      val labels = edge.getFlatLabels()
      if (labels.none { it is InvokeLabel && it.name in STUBS && it.name !in defined }) continue
      val rewritten =
        labels.flatMap { label ->
          if (label is InvokeLabel && label.name in STUBS && label.name !in defined)
            stub(label, builder)
          else listOf(label)
        }
      builder.removeEdge(edge)
      builder.addEdge(edge.withLabel(SequenceLabel(rewritten, edge.label.metadata)))
    }
    return builder
  }

  private fun stub(invoke: InvokeLabel, builder: XcfaProcedureBuilder): List<XcfaLabel> {
    val out = mutableListOf<XcfaLabel>()
    uniqueWarningLogger.write(
      Logger.Level.INFO,
      "WARNING: %s is stubbed -- its return value is nondeterministic%s.\n",
      invoke.name,
      if (STUBS[invoke.name].isNullOrEmpty()) "" else " and the buffers it writes are havoced",
    )

    // The buffers it writes: unconstrained beats stale.
    for (i in STUBS[invoke.name].orEmpty()) {
      if (i >= invoke.params.size) continue
      val ptr = invoke.params[i]
      val cell = pointeeCellType(ptr) ?: continue
      for (n in 0 until DEFAULT_FILL_CELLS) {
        val fresh = Var("__stub_${invoke.name}_${counter++}", cell.smtType)
        builder.addVar(fresh)
        val index = CComplexType.getUnsignedLong(parseContext).getValue("$n")
        val deref =
          Dereference.of(
            ptr as Expr<Type>,
            cast(index, ptr.type) as Expr<Type>,
            cell.smtType as Type,
          )
        parseContext.metadata.create(deref, "cType", CPointer(null, cell, parseContext))
        out.add(StmtLabel(HavocStmt.of(fresh), metadata = invoke.metadata))
        // Bound it to the cell's C type, exactly as a `__VERIFIER_nondet_<type>()` result is
        // bounded. A bare havoc is unconstrained across its whole SMT sort, and under integer
        // arithmetic that sort is the UNBOUNDED integers, so without this a stubbed read can hand
        // back a value no object of that type could hold.
        //
        // MEASURED, on real inputs: this turns the whole Juliet CWE190 `_good` family from
        // `false(no-overflow)` into correct `true` -- 25 of 25 sampled tasks that were wrong in
        // run 98 -- while all 8 sampled `_bad` counterparts still report the real overflow, so the
        // assume is not suppressing genuine bugs. What is NOT established is the precise chain
        // from the missing bound to that verdict: five minimal programs of the obvious shape
        // (one-sided guard over a stub-written value, both data models, both arithmetics) all
        // verify Safe with and without this line, so something else in those files participates.
        // Treat the mechanism as open; the evidence for the fix is the real-task measurement.
        //
        // Emitted here rather than left to [HavocPromotionAndRange], which adds exactly this assume
        // but runs BEFORE this pass in the pipeline, so a havoc introduced here never reaches it --
        // stamping `cType` on the variable to make that pass pick it up was tried and measured at
        // zero effect for the same reason.
        out.add(StmtLabel(cell.limit(fresh.ref), metadata = invoke.metadata))
        out.add(
          StmtLabel(
            MemoryAssignStmt.create(deref, cast(fresh.ref, cell.smtType)),
            metadata = invoke.metadata,
          )
        )
      }
    }

    // The return value.
    val ret = (invoke.params.getOrNull(0) as? RefExpr<*>)?.decl as? VarDecl<*>
    if (ret != null) out.add(StmtLabel(HavocStmt.of(ret), metadata = invoke.metadata))
    return out
  }

  /** The cell type a written pointer argument points at, when it is a scalar we can fill. */
  private fun pointeeCellType(ptr: Expr<*>): CComplexType? {
    val pointee =
      when (val t = CComplexType.getType(ptr, parseContext)) {
        is CPointer -> t.embeddedType
        is CArray -> t.embeddedType
        else -> null
      } ?: return null
    return if (pointee is CStruct || pointee is CArray || pointee is CVoid) null else pointee
  }
}
