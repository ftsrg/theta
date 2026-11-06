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
import hu.bme.mit.theta.core.type.LitExpr
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
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.STATIC_OBJECT
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.typeInterval

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
 * easily as invent one, where unconstrained is a safe over-approximation. It is safe for a Safe
 * verdict only, so each value made up here is recorded in [XcfaBuilder.overApproximatedVars].
 *
 * Under the memory-safety properties a call also leaves markers for what it reads and writes, which
 * [FormatAccessPass] resolves. Only `*printf`, `puts` and `fputs` do; other stubs access nothing
 * the guards see.
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
       * caller passed beyond it -- `fscanf(f, "%d %d %d %d %d", &a, &b, &c, &d, &e)` would leave
       * `e` holding its old value while the program believes it was read. That is an
       * under-approximation in the dangerous direction: a stale value is one specific value, and a
       * program that branches on it can be proved safe on the strength of it.
       */
      data class VariadicFrom(val from: Int) : Writes
    }

    /**
     * @param writes what the call stores through its arguments.
     * @param returns a fixed return value for a call that is assumed always to succeed, or null to
     *   havoc the return. A havoc'd return means the caller's error path is always reachable, which
     *   invents failures the modelled program cannot have; where the standard assumption is
     *   success, say so here instead.
     * @param input the written buffers hold input from the environment, which can be any value in C
     *   too. Otherwise the call computes them, and their havoc is an over-approximation.
     * @param freshString the call returns a string in static storage of fewer than this many
     *   characters, with any content.
     */
    private data class Stub(
      val writes: Writes = Writes.None,
      val returns: Long? = null,
      val input: Boolean = false,
      val freshString: Int? = null,
    )

    private val STUBS: Map<String, Stub> =
      mapOf(
        // stdio: reads produce nondeterministic data in the caller's buffer
        "fgets" to Stub(Writes.At(setOf(1)), input = true),
        "fscanf" to Stub(Writes.VariadicFrom(3), input = true), // (ret, stream, fmt, &a, &b, ...)
        "__isoc99_fscanf" to Stub(Writes.VariadicFrom(3), input = true),
        "scanf" to Stub(Writes.VariadicFrom(2), input = true), // (ret, fmt, &a, &b, ...)
        "__isoc99_scanf" to Stub(Writes.VariadicFrom(2), input = true),
        "sscanf" to Stub(Writes.VariadicFrom(3)),
        "__isoc99_sscanf" to Stub(Writes.VariadicFrom(3)),
        "read" to Stub(Writes.At(setOf(2)), input = true),
        "fread" to Stub(Writes.At(setOf(1)), input = true),
        "getline" to Stub(Writes.At(setOf(1, 2)), input = true),
        // stdio: writes go to a stream we do not model, so only the return matters
        "fopen" to Stub(),
        "fclose" to Stub(),
        "fflush" to Stub(),
        "printf" to Stub(),
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
        // string/memory inspection -- these only READ, so the return is the whole effect.
        // CLibraryFunctionsPass models most `strlen` calls exactly; this stub takes the rest.
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
        // glibc and musl messages in the C locale are shorter than this
        "strerror" to Stub(freshString = 128),
      )

    /** The argument position of the format, for the calls that read their `%s` arguments. */
    private val READ_FORMAT_INDEX =
      mapOf("printf" to 1, "fprintf" to 2, "sprintf" to 2, "snprintf" to 3, "asprintf" to 2)

    /** The calls whose first argument is a string they read; `perror` also takes NULL. */
    private val STRING_ARGUMENT = setOf("puts", "fputs")

    /** The argument position of the format, for the calls whose return a format bounds. */
    private val FORMAT_INDEX =
      mapOf(
        "sprintf" to 2,
        "snprintf" to 3,
        "vsnprintf" to 3,
        "asprintf" to 2,
        "vasprintf" to 2,
        "fprintf" to 2,
      )

    /** The stubbed calls that write through a pointer, filling only [DEFAULT_FILL_CELLS] cells. */
    internal val BUFFER_WRITING: Set<String> = STUBS.filterValues { it.writes != Writes.None }.keys

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
          if (label is InvokeLabel && label.stubbable(defined)) stub(label, builder)
          else listOf(label)
        }
      builder.removeEdge(edge)
      builder.addEdge(edge.withLabel(SequenceLabel(rewritten, edge.label.metadata)))
    }
    return builder
  }

  /**
   * A call this pass may replace: a known stub, not defined in the XCFA, and **not flagged for
   * specific handling**. The flag is the whole point of [InvokeLabel.isLibraryFunction] --
   * something downstream models this call properly, and a havoc here would silently replace that
   * model.
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

    // The call reads every argument it is given, and replacing the InvokeLabel with havocs would
    // drop those expressions along with it -- so `fprintf(f, "%d", shared)` would stop being an
    // access to `shared` at all, and a data race on it would go unreported. Materialise each
    // argument as a read into a fresh variable first, the way CLibraryFunctionsPass models
    // `printf`. This is the argument *value*; what a pointer argument points AT is a separate
    // question, answered (for the written buffers only) below.
    var format: VarDecl<*>? = null
    val arguments = invoke.params.toMutableList<Expr<*>>()
    for (i in 1 until invoke.params.size) {
      val arg = invoke.params[i]
      if (arg is LitExpr<*>) continue // a constant reads nothing
      val read = Var("__stub_${invoke.name}_arg_${counter++}", arg.type)
      builder.addVar(read)
      out.add(AssignStmtLabel(read, arg, metadata = invoke.metadata))
      arguments[i] = read.ref
      if (i == FORMAT_INDEX[invoke.name]) format = read
    }
    if (parseContext.isCheckMemsafety) out.addAll(accessMarkers(invoke, arguments, builder))
    if (written.isNotEmpty()) builder.parent.bufferStubCalls++

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
        if (!spec.input) builder.overApproximatedVars[fresh] = typeInterval(cell, parseContext)
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
        // Emitted here: [HavocPromotionAndRange] bounds only a variable with a `cType`.
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
    if (ret != null && spec.freshString != null) {
      val string = freshString(ret, spec.freshString, invoke, builder)
      if (string != null) return out + string
    }
    if (ret != null && format != null && spec.returns == null) {
      builder.parent.formatArguments[ret] = format
    }
    if (ret != null) {
      val fixed = spec.returns
      if (fixed == null) {
        out.add(StmtLabel(HavocStmt.of(ret), metadata = invoke.metadata))
        builder.overApproximatedVars[ret] = typeInterval(ret.ref, parseContext)
      } else {
        val type = CComplexType.getType(ret.ref, parseContext)
        out.add(
          AssignStmtLabel(ret, cast(type.getValue("$fixed"), ret.type), metadata = invoke.metadata)
        )
      }
    }
    return out
  }

  /** What the guards need of this call; `arguments` hold the values it reads. */
  private fun accessMarkers(
    invoke: InvokeLabel,
    arguments: List<Expr<*>>,
    builder: XcfaProcedureBuilder,
  ): List<XcfaLabel> {
    fun marker(name: String, params: List<Expr<*>>) =
      InvokeLabel(name, params, metadata = invoke.metadata)
    if (invoke.name in STRING_ARGUMENT && arguments.size > 1) {
      return listOf(marker(FormatAccessPass.PLAIN_STRING_READ, listOf(arguments[1])))
    }
    val formatAt = READ_FORMAT_INDEX[invoke.name]?.takeIf { it < arguments.size } ?: return listOf()
    val format = (arguments[formatAt] as? RefExpr<*>)?.decl as? VarDecl<*> ?: return listOf()
    val id = builder.parent.formatMarkers.size
    builder.parent.formatMarkers[id] = format
    val marker = CComplexType.getSignedInt(parseContext).getValue("$id")
    val rest = arguments.subList(formatAt + 1, arguments.size)
    return listOfNotNull(
      marker(FormatAccessPass.FORMAT_READS, listOf(marker) + rest),
      if (invoke.name == "sprintf") {
        marker(FormatAccessPass.FORMAT_WRITE, listOf(marker, arguments[1]) + rest)
      } else null,
      if (invoke.name == "snprintf") {
        marker(
          FormatAccessPass.FORMAT_WRITE_BOUNDED,
          listOf(marker, arguments[1], invoke.params[2]) + rest,
        )
      } else null,
    )
  }

  /**
   * `ret` := a fresh static object of [cells] cells, with any characters in all cells but the last,
   * which is 0. Static, as C gives it: not a leak, and not a heap block to free. A fresh object per
   * call rather than one shared buffer, whose rewrites would race between threads. Null when [ret]
   * is not a pointer to a scalar.
   */
  private fun freshString(
    ret: VarDecl<*>,
    cells: Int,
    invoke: InvokeLabel,
    builder: XcfaProcedureBuilder,
  ): List<XcfaLabel>? {
    val cell = pointeeCellType(ret.ref) ?: return null
    val out = mutableListOf<XcfaLabel>()
    val size = CComplexType.getUnsignedLong(parseContext).getValue("$cells")
    out.add(InvokeLabel(STATIC_OBJECT, listOf(ret.ref, size), invoke.metadata))
    for (n in 0 until cells) {
      val index = CComplexType.getUnsignedLong(parseContext).getValue("$n")
      val deref =
        Dereference.of(
          ret.ref as Expr<Type>,
          cast(index, ret.type) as Expr<Type>,
          cell.smtType as Type,
        )
      parseContext.metadata.create(deref, "cType", CPointer(null, cell, parseContext))
      val value =
        if (n == cells - 1) cell.nullValue
        else {
          val fresh = Var("__stub_${invoke.name}_${counter++}", cell.smtType)
          builder.addVar(fresh)
          builder.overApproximatedVars[fresh] = typeInterval(cell, parseContext)
          out.add(StmtLabel(HavocStmt.of(fresh), metadata = invoke.metadata))
          out.add(StmtLabel(cell.limit(fresh.ref), metadata = invoke.metadata))
          fresh.ref
        }
      out.add(
        StmtLabel(
          MemoryAssignStmt.create(deref, cast(value, cell.smtType)),
          metadata = invoke.metadata,
        )
      )
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
