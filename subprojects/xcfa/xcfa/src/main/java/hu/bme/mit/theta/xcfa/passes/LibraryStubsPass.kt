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
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Div
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Rem
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.asConstantBigInteger
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.typeInterval
import java.math.BigInteger

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
     * @param freshString the call returns a fresh string of fewer than this many characters, with
     *   any content.
     * @param model an exact model of the call, used where it applies.
     * @param envReturn the environment gives a return value in `[lo, hi]` (`hi` null: the type's
     *   maximum), each one possible in C.
     */
    private data class Stub(
      val writes: Writes = Writes.None,
      val returns: Long? = null,
      val input: Boolean = false,
      val freshString: Int? = null,
      val model: Model = Model.Plain,
      val envReturn: EnvReturn? = null,
    )

    private data class EnvReturn(val lo: Long, val hi: Long?)

    /** An exact model. Where it does not apply (e.g., a symbolic size), the plain stub is used. */
    private sealed interface Model {
      object Plain : Model

      /** `scanf` family: the arguments from [from] on are read, `EOF` or their count returned. */
      data class Scan(val from: Int, val format: Int) : Model

      /** `fgets(buf, n, stream)`: a line of 1 to `n - 1` characters, or NULL. */
      object Line : Model

      /** `read`/`recv(fd, buf, n, ...)`: -1, or `r <= n` bytes in `buf[0 .. r-1]`. */
      object Receive : Model

      /** `htons` and friends on a little-endian target: reverse the [bytes] bytes. */
      data class ByteSwap(val bytes: Int) : Model

      /** `inet_addr` of a string literal: its value in network byte order. */
      object InetAddr : Model
    }

    private val STUBS: Map<String, Stub> =
      mapOf(
        // stdio: reads produce nondeterministic data in the caller's buffer
        "fgets" to Stub(Writes.At(setOf(1)), input = true, model = Model.Line),
        "fscanf" to scan(3, 2), // (ret, stream, fmt, &a, &b, ...)
        "__isoc99_fscanf" to scan(3, 2),
        "scanf" to scan(2, 1), // (ret, fmt, &a, &b, ...)
        "__isoc99_scanf" to scan(2, 1),
        "sscanf" to Stub(Writes.VariadicFrom(3)),
        "__isoc99_sscanf" to Stub(Writes.VariadicFrom(3)),
        "read" to Stub(Writes.At(setOf(2)), input = true, model = Model.Receive),
        "recv" to Stub(Writes.At(setOf(2)), input = true, model = Model.Receive),
        "fread" to Stub(Writes.At(setOf(1)), input = true),
        "getline" to Stub(Writes.At(setOf(1, 2)), input = true),
        // sockets: success depends on the environment (POSIX return values)
        "socket" to Stub(envReturn = EnvReturn(-1, null)),
        "accept" to Stub(envReturn = EnvReturn(-1, null)), // only with NULL address arguments
        "connect" to Stub(envReturn = EnvReturn(-1, 0)),
        "bind" to Stub(envReturn = EnvReturn(-1, 0)),
        "listen" to Stub(envReturn = EnvReturn(-1, 0)),
        "shutdown" to Stub(envReturn = EnvReturn(-1, 0)),
        "close" to Stub(envReturn = EnvReturn(-1, 0)),
        "inet_addr" to Stub(model = Model.InetAddr),
        "htons" to Stub(model = Model.ByteSwap(2)),
        "ntohs" to Stub(model = Model.ByteSwap(2)),
        "htonl" to Stub(model = Model.ByteSwap(4)),
        "ntohl" to Stub(model = Model.ByteSwap(4)),
        // CLibraryFunctionsPass models these exactly where it can
        "atoi" to Stub(),
        "atol" to Stub(),
        "atoll" to Stub(),
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

    private fun scan(from: Int, format: Int) =
      Stub(Writes.VariadicFrom(from), input = true, model = Model.Scan(from, format))

    /** How many cells of a written pointee to fill when its extent is not otherwise known. */
    private const val DEFAULT_FILL_CELLS = 1

    /** The largest constant buffer size that [Model.Line] and [Model.Receive] fill cell by cell. */
    private const val MAX_EXACT_CELLS = 256

    /**
     * True if the call is a stub that writes a buffer but leaves some cells stale that C writes,
     * e.g., `sprintf` or `fgets` with a symbolic size. An exact reader of those cells (`strlen`,
     * `atoi`) could then prove a wrong Safe.
     */
    internal fun writesBufferInexactly(invoke: InvokeLabel, parseContext: ParseContext): Boolean {
      val spec = STUBS[invoke.name] ?: return false
      if (spec.writes == Writes.None) return false
      return when (val model = spec.model) {
        Model.Line -> exactExtent(invoke, 1, 2, parseContext) == null
        Model.Receive -> exactExtent(invoke, 2, 3, parseContext) == null
        is Model.Scan ->
          // a `char` target may be a `%s` conversion, which writes a whole string
          (model.from until invoke.params.size).any { i ->
            val arg = invoke.params[i]
            val target = scalarTarget(arg, parseContext)
            val type = target?.let { CComplexType.getType(it, parseContext) }
            (type ?: pointeeCellType(arg, parseContext)).let { it == null || it.width() <= 8 }
          }
        is Model.ByteSwap,
        Model.InetAddr,
        Model.Plain -> true
      }
    }

    /**
     * The constant size `n` of the buffer argument [buffer] when its cells can be written one by
     * one: a plain variable of scalar cells, and `n` (argument [size]) at most [MAX_EXACT_CELLS].
     */
    private fun exactExtent(
      invoke: InvokeLabel,
      buffer: Int,
      size: Int,
      parseContext: ParseContext,
    ): Int? {
      val ptr = invoke.params.getOrNull(buffer) as? RefExpr<*> ?: return null
      pointeeCellType(ptr, parseContext) ?: return null
      val n = invoke.params.getOrNull(size)?.let { ExprUtils.simplify(it).asConstantBigInteger() }
      return n?.takeIf { it.signum() >= 0 && it <= MAX_EXACT_CELLS.toBigInteger() }?.toInt()
    }

    /** `x` for an argument `&x` of a variable of an integer type other than a pointer. */
    private fun scalarTarget(arg: Expr<*>, parseContext: ParseContext): RefExpr<*>? {
      val target = (arg as? Reference<*, *>)?.expr as? RefExpr<*> ?: return null
      if (target.decl !is VarDecl<*>) return null
      val type = CComplexType.getType(target, parseContext)
      return target.takeIf {
        type is CInteger && type !is CPointer && type !is CArray && type !is CStruct
      }
    }

    /** The cell type a written pointer argument points at, when it is a scalar we can fill. */
    private fun pointeeCellType(ptr: Expr<*>, parseContext: ParseContext): CComplexType? {
      val pointee =
        when (val t = CComplexType.getType(ptr, parseContext)) {
          is CPointer -> t.embeddedType
          is CArray -> t.embeddedType
          else -> null
        } ?: return null
      return if (pointee is CStruct || pointee is CArray || pointee is CVoid) null else pointee
    }
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
    name in STUBS &&
      name !in defined &&
      !isLibraryFunction &&
      // a fresh string is allocated, which memory safety would report as a leak
      !(STUBS.getValue(name).freshString != null && parseContext.isCheckMemsafety) &&
      // the address arguments would be written
      (name != "accept" || params.drop(2).all { isNullLiteral(it) })

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
    val model = spec.model
    for (i in 1 until invoke.params.size) {
      val arg = invoke.params[i]
      if (arg is LitExpr<*>) continue // a constant reads nothing
      // `&x` is not read, and keeping it would put `x` into memory
      if (model is Model.Scan && i >= model.from && scalarTarget(arg, parseContext) != null)
        continue
      val read = Var("__stub_${invoke.name}_arg_${counter++}", arg.type)
      builder.addVar(read)
      out.add(AssignStmtLabel(read, arg, metadata = invoke.metadata))
      if (i == FORMAT_INDEX[invoke.name]) format = read
    }

    val exact =
      when (model) {
        is Model.Scan -> scan(invoke, model, builder)
        Model.Line -> line(invoke, builder)
        Model.Receive -> receive(invoke, builder)
        is Model.ByteSwap -> byteSwap(invoke, model.bytes)
        Model.InetAddr -> inetAddr(invoke, builder)
        Model.Plain -> null
      }
    if (exact != null) return out + exact

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
      if (spec.envReturn != null) {
        val hi = spec.envReturn.hi
        out.addAll(havocWithin(ret, spec.envReturn.lo, hi?.toBigInteger(), invoke))
      } else if (fixed == null) {
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

  /**
   * `ret := malloc(cells)`, never null, with any characters in all cells but the last, which is 0.
   * Null when [ret] is not a pointer to a scalar.
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
    out.add(InvokeLabel("malloc", listOf(ret.ref, size), invoke.metadata))
    val nullValue = CComplexType.getType(ret.ref, parseContext).nullValue
    out.add(StmtLabel(Assume(Neq(ret.ref, nullValue)), metadata = invoke.metadata))
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

  private fun pointeeCellType(ptr: Expr<*>): CComplexType? = pointeeCellType(ptr, parseContext)

  /** `havoc v; lo <= v <= hi` (`hi` null: the type's maximum). The environment chooses `v`. */
  private fun havocWithin(
    v: VarDecl<*>,
    lo: Long,
    hi: BigInteger?,
    invoke: InvokeLabel,
  ): List<XcfaLabel> {
    val type = CComplexType.getType(v.ref, parseContext)
    val bounds =
      listOfNotNull(Geq(v.ref, type.getValue("$lo")), hi?.let { Leq(v.ref, type.getValue("$it")) })
    return listOf(
      StmtLabel(HavocStmt.of(v), metadata = invoke.metadata),
      StmtLabel(type.limit(v.ref), metadata = invoke.metadata),
      StmtLabel(Assume(And(bounds as List<Expr<BoolType>>)), metadata = invoke.metadata),
    )
  }

  /** A fresh input value of the C type [type], bounded to that type. */
  private fun freshInput(
    type: CComplexType,
    invoke: InvokeLabel,
    builder: XcfaProcedureBuilder,
    out: MutableList<XcfaLabel>,
  ): RefExpr<*> {
    val fresh = Var("__stub_${invoke.name}_${counter++}", type.smtType)
    builder.addVar(fresh)
    out.add(StmtLabel(HavocStmt.of(fresh), metadata = invoke.metadata))
    out.add(StmtLabel(type.limit(fresh.ref), metadata = invoke.metadata))
    return fresh.ref
  }

  /** Cell [n] of the buffer [ptr] of [cell]s. */
  private fun cellAt(ptr: Expr<*>, n: Int, cell: CComplexType): Dereference<*, *, *> {
    val index = CComplexType.getUnsignedLong(parseContext).getValue("$n")
    val deref =
      Dereference.of(ptr as Expr<Type>, cast(index, ptr.type) as Expr<Type>, cell.smtType as Type)
    parseContext.metadata.create(deref, "cType", CPointer(null, cell, parseContext))
    return deref
  }

  private fun store(deref: Dereference<*, *, *>, value: Expr<*>, invoke: InvokeLabel) =
    StmtLabel(
      MemoryAssignStmt.create(deref as Dereference<*, *, Type>, cast(value, deref.type)),
      metadata = invoke.metadata,
    )

  /**
   * `scanf` family. The `i`-th target gets an input value of its type if the call returns at least
   * `i` (C11 7.21.6.2), else it keeps its value. A target `&x` becomes an assignment to `x`, so `x`
   * need not be in memory. If the format literal is not known, or has a `%n`, the return is
   * recorded as over-approximated and every target is havoced.
   */
  private fun scan(
    invoke: InvokeLabel,
    model: Model.Scan,
    builder: XcfaProcedureBuilder,
  ): List<XcfaLabel> {
    val out = mutableListOf<XcfaLabel>()
    val intType = CComplexType.getSignedInt(parseContext)
    val ret =
      (invoke.params.getOrNull(0) as? RefExpr<*>)?.decl as? VarDecl<*>
        ?: Var("__stub_${invoke.name}_ret_${counter++}", intType.smtType).also(builder::addVar)
    val targets = (model.from until invoke.params.size).toList()
    val conversions =
      invoke.params.getOrNull(model.format)?.let { format ->
        literalsOf(builder).textsOf(format)?.map { scanConversions(it) ?: return@let null }?.max()
      }
    val count = minOf(conversions ?: targets.size, targets.size)
    out.addAll(havocWithin(ret, -1, count.toBigInteger(), invoke))
    if (conversions == null) builder.overApproximatedVars[ret] = typeInterval(ret.ref, parseContext)
    val retType = CComplexType.getType(ret.ref, parseContext)
    for ((k, i) in targets.withIndex()) {
      if (k >= count) break // no conversion reads it
      val assigned: Expr<BoolType> =
        if (conversions == null) Bool(true) else Geq(ret.ref, retType.getValue("${k + 1}"))
      val arg = invoke.params[i]
      val target = scalarTarget(arg, parseContext)
      if (target != null) {
        val value = freshInput(CComplexType.getType(target, parseContext), invoke, builder, out)
        out.add(
          AssignStmtLabel(target, Ite<Type>(assigned, value, target), metadata = invoke.metadata)
        )
      } else {
        val cell = pointeeCellType(arg) ?: continue
        val deref = cellAt(arg, 0, cell)
        val value = freshInput(cell, invoke, builder, out)
        out.add(store(deref, Ite<Type>(assigned, value, deref), invoke))
      }
    }
    return out
  }

  /**
   * `fgets(buf, n, stream)` with a constant `n`: NULL with indeterminate cells, or `buf` with a
   * line of `k` in `[1, n-1]` characters, a `'\n'` only as the last one, and 0 after it.
   */
  private fun line(invoke: InvokeLabel, builder: XcfaProcedureBuilder): List<XcfaLabel>? {
    val n = exactExtent(invoke, 1, 2, parseContext)?.takeIf { it >= 2 } ?: return null
    val ret = (invoke.params[0] as? RefExpr<*>)?.decl as? VarDecl<*> ?: return null
    val buf = invoke.params[1]
    val cell = pointeeCellType(buf) ?: return null
    val out = mutableListOf<XcfaLabel>()
    val ok = Var("__stub_fgets_ok_${counter++}", Bool())
    builder.addVar(ok)
    out.add(StmtLabel(HavocStmt.of(ok), metadata = invoke.metadata))
    val intType = CComplexType.getSignedInt(parseContext)
    val k = Var("__stub_fgets_len_${counter++}", intType.smtType)
    builder.addVar(k)
    out.addAll(havocWithin(k, 1, (n - 1).toBigInteger(), invoke))
    val newline = cell.getValue("10")
    for (i in 0 until n) {
      val deref = cellAt(buf, i, cell)
      val value = freshInput(cell, invoke, builder, out)
      if (i + 1 < n - 1) {
        val inside = And(ok.ref, Lt(intType.getValue("${i + 1}"), k.ref))
        out.add(StmtLabel(Assume(Or(Not(inside), Neq(value, newline))), metadata = invoke.metadata))
      }
      val read =
        Ite<Type>(
          Lt(intType.getValue("$i"), k.ref),
          value,
          Ite<Type>(Eq(intType.getValue("$i"), k.ref), cell.nullValue, deref),
        )
      out.add(store(deref, Ite<Type>(ok.ref, read, value), invoke))
    }
    val retType = CComplexType.getType(ret.ref, parseContext)
    out.add(
      AssignStmtLabel(
        ret,
        Ite<Type>(ok.ref, cast(buf, ret.type), cast(retType.nullValue, ret.type)),
        metadata = invoke.metadata,
      )
    )
    return out
  }

  /** `read`/`recv(fd, buf, n, ...)` with a constant `n`: -1, or `r <= n` input bytes in `buf`. */
  private fun receive(invoke: InvokeLabel, builder: XcfaProcedureBuilder): List<XcfaLabel>? {
    val n = exactExtent(invoke, 2, 3, parseContext) ?: return null
    val ret = (invoke.params[0] as? RefExpr<*>)?.decl as? VarDecl<*> ?: return null
    val buf = invoke.params[2]
    val cell = pointeeCellType(buf) ?: return null
    val out = mutableListOf<XcfaLabel>()
    out.addAll(havocWithin(ret, -1, n.toBigInteger(), invoke))
    val retType = CComplexType.getType(ret.ref, parseContext)
    for (i in 0 until n) {
      val deref = cellAt(buf, i, cell)
      val value = freshInput(cell, invoke, builder, out)
      out.add(store(deref, Ite<Type>(Lt(retType.getValue("$i"), ret.ref), value, deref), invoke))
    }
    return out
  }

  /** `ret := x` with its bytes reversed, from the remainders of `x` divided by powers of 256. */
  private fun byteSwap(invoke: InvokeLabel, bytes: Int): List<XcfaLabel>? {
    val ret = (invoke.params[0] as? RefExpr<*>)?.decl as? VarDecl<*> ?: return null
    val type = CComplexType.getType(ret.ref, parseContext)
    if (type !is CInteger || type.isSsigned || type.width() != bytes * 8) return null
    val x = type.castTo(invoke.params.getOrNull(1) ?: return null)
    val num = { v: BigInteger -> type.getValue("$v") }
    val byte = BigInteger.valueOf(256)
    val swapped =
      (0 until bytes)
        .map<Int, Expr<*>> { k ->
          Mul(Rem(Div(x, num(byte.pow(k))), num(byte)), num(byte.pow(bytes - 1 - k)))
        }
        .reduce { a, b -> Add(a, b) }
    return listOf(AssignStmtLabel(ret, cast(swapped, ret.type), metadata = invoke.metadata))
  }

  /** `inet_addr(s)` for a string literal `s`, parsed as glibc's `inet_aton` does. */
  private fun inetAddr(invoke: InvokeLabel, builder: XcfaProcedureBuilder): List<XcfaLabel>? {
    val ret = (invoke.params[0] as? RefExpr<*>)?.decl as? VarDecl<*> ?: return null
    val text = literalsOf(builder).textsOf(invoke.params.getOrNull(1) ?: return null)
    val host = text?.singleOrNull()?.let { parseIpv4(it) ?: 0xffffffffL } ?: return null
    // network byte order, read back as a little-endian integer
    val value =
      (0 until 4).fold(0L) { acc, k -> acc or (((host shr (8 * k)) and 0xff) shl (8 * (3 - k))) }
    val type = CComplexType.getType(ret.ref, parseContext)
    return listOf(
      AssignStmtLabel(ret, cast(type.getValue("$value"), ret.type), metadata = invoke.metadata)
    )
  }

  private var literals: Pair<XcfaBuilder, StringLiterals>? = null

  private fun literalsOf(builder: XcfaProcedureBuilder): StringLiterals =
    literals?.takeIf { it.first === builder.parent }?.second
      ?: StringLiterals(builder.parent).also { literals = builder.parent to it }
}

/**
 * The number of arguments that the `scanf` format [format] assigns and counts, or null if it has a
 * `%n` (assigned but not counted) or cannot be parsed.
 */
internal fun scanConversions(format: String): Int? {
  var count = 0
  var i = 0
  while (i < format.length) {
    if (format[i++] != '%') continue
    if (i < format.length && format[i] == '%') {
      i++
      continue
    }
    val suppressed = i < format.length && format[i] == '*'
    if (suppressed) i++
    while (i < format.length && (format[i].isDigit() || format[i] in "hljztL")) i++
    if (i >= format.length) return null
    when (format[i++]) {
      'n' -> return null
      '[' -> {
        if (i < format.length && format[i] == '^') i++
        if (i < format.length && format[i] == ']') i++
        while (i < format.length && format[i] != ']') i++
        if (i++ >= format.length) return null
      }
    }
    if (!suppressed) count++
  }
  return count
}

/**
 * The host-order value of an IPv4 address in the forms of `inet_aton` (`a.b.c.d`, `a.b.c`, `a.b`,
 * `a`; each part decimal, octal or hexadecimal), or null if it is invalid.
 */
internal fun parseIpv4(text: String): Long? {
  val address = text.takeWhile { !it.isWhitespace() }
  val parts =
    address.split('.').map { part ->
      when {
        part.isEmpty() -> return null
        part.startsWith("0x") || part.startsWith("0X") -> part.drop(2).toLongOrNull(16)
        part.length > 1 && part.startsWith("0") -> part.drop(1).toLongOrNull(8)
        else -> part.toLongOrNull(10)
      }?.takeIf { it >= 0 } ?: return null
    }
  if (parts.size > 4) return null
  val last = parts.last()
  val lastBits = 8 * (5 - parts.size)
  if (parts.dropLast(1).any { it > 255 } || last >= (1L shl lastBits)) return null
  return parts.dropLast(1).foldIndexed(last) { i, acc, part -> acc or (part shl (24 - 8 * i)) }
}
