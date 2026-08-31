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
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
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
 * reaches the analysis as a procedure that does not exist -- "No such method fscanf" and friends.
 *
 * These are stubbed explicitly instead. Each entry states which arguments the function WRITES
 * THROUGH, and those pointees are filled with fresh nondeterministic values rather than being left
 * at their old contents -- leaving them would be a specific wrong value, which can hide a bug as
 * easily as invent one, where unconstrained is a safe over-approximation.
 *
 * ⚠️ Not modelled here, deliberately:
 * - a call flagged [InvokeLabel.isLibraryFunction]. That flag means "an later pass or the analysis
 *   handles this one specifically" -- [CLibraryFunctionsPass] sets it on the thread-specific-key
 *   family, which the OC checker supports properly. Stubbing such a call to a havoc throws that
 *   support away, so this pass skips them exactly as [UnresolvedInvokeToHavocPass] does.
 * - anything an earlier pass already consumes ([CLibraryFunctionsPass] takes `printf` and `scanf`,
 *   and models them better than a stub could: it materialises `printf`'s argument reads so a data
 *   race on them stays visible, and havocs *every* `scanf` argument rather than a fixed few).
 * - `setjmp`/`longjmp` (non-local control flow -- a havoc would be a wrong program) and the math
 *   functions (`sin`, `expf`, ...), whose *values* matter to their callers; a havoc there turns a
 *   precise computation into noise and answers float tasks by accident.
 */
class LibraryStubsPass(val parseContext: ParseContext, val uniqueWarningLogger: Logger) :
  ProcedurePass {

  companion object {

    /**
     * What a stubbed call writes through its arguments.
     *
     * `params[0]` is the return slot, so the C arguments start at 1.
     */
    private sealed interface Writes {
      /** Nothing the model can see: the call's whole effect is its return value. */
      object None : Writes

      /** Exactly these argument positions. */
      data class At(val indices: Set<Int>) : Writes

      /**
       * Every pointer argument from [from] onwards.
       *
       * The `scanf` family is **variadic**, so a fixed set of indices silently ignores whatever the
       * caller passed beyond it -- `fscanf(f, "%d %d %d %d %d", &a, &b, &c, &d, &e)` would leave `e`
       * holding its old value while the program believes it was read. That is an
       * under-approximation in the dangerous direction: a stale value is one specific value, and a
       * program that branches on it can be proved safe on the strength of it.
       */
      data class VariadicFrom(val from: Int) : Writes
    }

    /**
     * @param writes what the call stores through its arguments.
     * @param returns a fixed return value for a call that is assumed always to succeed, or null to
     *   havoc the return. A havoc'd return means the caller's error path is always reachable, which
     *   invents failures the modelled program cannot have; where the standard assumption is success,
     *   say so here instead.
     */
    private data class Stub(val writes: Writes = Writes.None, val returns: Long? = null)

    private val STUBS: Map<String, Stub> =
      mapOf(
        // stdio: reads produce nondeterministic data in the caller's buffer
        "fgets" to Stub(Writes.At(setOf(1))),
        "fscanf" to Stub(Writes.VariadicFrom(3)), // (ret, stream, fmt, &a, &b, ...)
        "__isoc99_fscanf" to Stub(Writes.VariadicFrom(3)),
        "__isoc99_scanf" to Stub(Writes.VariadicFrom(2)), // (ret, fmt, &a, &b, ...)
        "sscanf" to Stub(Writes.VariadicFrom(3)),
        "__isoc99_sscanf" to Stub(Writes.VariadicFrom(3)),
        "read" to Stub(Writes.At(setOf(2))),
        "fread" to Stub(Writes.At(setOf(1))),
        "getline" to Stub(Writes.At(setOf(1, 2))),
        // stdio: writes go to a stream we do not model, so only the return matters
        "fopen" to Stub(),
        "fclose" to Stub(),
        "fflush" to Stub(),
        "fprintf" to Stub(),
        "puts" to Stub(),
        "fputs" to Stub(),
        "fputc" to Stub(),
        "putchar" to Stub(),
        "perror" to Stub(),
        "fwrite" to Stub(),
        // formatting into a caller buffer
        "sprintf" to Stub(Writes.At(setOf(1))),
        "snprintf" to Stub(Writes.At(setOf(1))),
        "vsnprintf" to Stub(Writes.At(setOf(1))),
        "vasprintf" to Stub(Writes.At(setOf(1))),
        "asprintf" to Stub(Writes.At(setOf(1))),
        // string/memory inspection -- these only READ, so the return is the whole effect
        "strlen" to Stub(),
        "strnlen" to Stub(),
        "strcmp" to Stub(),
        "strncmp" to Stub(),
        "strcasecmp" to Stub(),
        "memcmp" to Stub(),
        "strchr" to Stub(),
        "strrchr" to Stub(),
        "strstr" to Stub(),
        "strspn" to Stub(),
        "strcspn" to Stub(),
        "strpbrk" to Stub(),
        // Registering an exit handler cannot fail in this model, and a havoc'd return would make
        // `if (atexit(f)) abort();` reachable in a program where it is not.
        "atexit" to Stub(returns = 0),
        "on_exit" to Stub(returns = 0),
        "at_quick_exit" to Stub(returns = 0),
      )

    /** How many cells of a written pointee to fill when its extent is not otherwise known. */
    private const val DEFAULT_FILL_CELLS = 1
  }

  private var counter = 0

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val defined = builder.parent.getProcedures().mapNotNull { it.name }.toSet()
    for (edge in ArrayList(builder.getEdges())) {
      val labels = edge.getFlatLabels()
      if (labels.none { it is InvokeLabel && it.stubbable(defined) }) continue
      val rewritten =
        labels.flatMap { label ->
          if (label is InvokeLabel && label.stubbable(defined)) stub(label, builder) else listOf(label)
        }
      builder.removeEdge(edge)
      builder.addEdge(edge.withLabel(SequenceLabel(rewritten, edge.label.metadata)))
    }
    return builder
  }

  /**
   * A call this pass may replace: a known stub, not defined in the XCFA, and **not flagged for
   * specific handling**. The flag is the whole point of [InvokeLabel.isLibraryFunction] -- something
   * downstream models this call properly, and a havoc here would silently replace that model.
   */
  private fun InvokeLabel.stubbable(defined: Set<String>) =
    name in STUBS && name !in defined && !isLibraryFunction

  /** The argument positions this call writes through, resolved against the actual arity. */
  private fun writtenIndices(stub: Stub, invoke: InvokeLabel): List<Int> =
    when (val w = stub.writes) {
      is Writes.None -> emptyList()
      is Writes.At -> w.indices.filter { it < invoke.params.size }
      is Writes.VariadicFrom -> (w.from until invoke.params.size).toList()
    }

  private fun stub(invoke: InvokeLabel, builder: XcfaProcedureBuilder): List<XcfaLabel> {
    val out = mutableListOf<XcfaLabel>()
    val spec = STUBS.getValue(invoke.name)
    val written = writtenIndices(spec, invoke)
    uniqueWarningLogger.write(
      Logger.Level.INFO,
      "WARNING: %s is stubbed -- its return value is %s%s.\n",
      invoke.name,
      if (spec.returns != null) "${spec.returns}" else "nondeterministic",
      if (written.isEmpty()) "" else " and the buffers it writes are havoced",
    )

    // The buffers it writes: unconstrained beats stale.
    for (i in written) {
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
        // ⚠️ The effect is measured on real inputs but the mechanism is NOT understood: removing
        // this line turns a whole family of correct `true` overflow verdicts into false alarms,
        // while their buggy counterparts still report the real overflow -- yet minimal programs of
        // the obvious shape (a one-sided guard over a stub-written value) verify the same with and
        // without it. Something else in those inputs participates. Do not remove it on the grounds
        // that a small repro shows no difference.
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

    // The return value: a fixed one where the call is assumed to succeed, otherwise a havoc.
    val ret = (invoke.params.getOrNull(0) as? RefExpr<*>)?.decl as? VarDecl<*>
    if (ret != null) {
      val fixed = spec.returns
      if (fixed == null) {
        out.add(StmtLabel(HavocStmt.of(ret), metadata = invoke.metadata))
      } else {
        val type = CComplexType.getType(ret.ref, parseContext)
        out.add(AssignStmtLabel(ret, cast(type.getValue("$fixed"), ret.type), metadata = invoke.metadata))
      }
    }
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
