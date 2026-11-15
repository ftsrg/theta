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
package hu.bme.mit.theta.xcfa.passes.library

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Dereference
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.HavocStmtLabel
import hu.bme.mit.theta.xcfa.utils.STATIC_OBJECT
import hu.bme.mit.theta.xcfa.utils.asConstantBigInteger
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.withinTypeRange
import java.math.BigInteger

/**
 * Gives `main(int argc, char *argv[])` the arguments C17 5.1.2.2.1 describes: `argc` is not
 * negative, `argv[argc]` is a null pointer, and `argv[0]` to `argv[argc - 1]` point to strings of
 * any length. The array and the strings are modifiable static objects, so they are neither freed
 * nor leaked. The array and the strings are objects, so their sizes are at most `PTRDIFF_MAX` bytes
 * (GCC's maximum object size).
 *
 * Only memory safety sees the size of a string, so only there is every character but the last one
 * set to a value other than 0 (a loop over the string): otherwise a string whose first 0 comes
 * early is indistinguishable from a shorter one. When `main` reads `argv` at constant indices only,
 * just those strings are created, without a loop over `argc`. Unused arguments are left alone.
 */
class EntryArgumentsPass(private val parseContext: ParseContext) : ProcedurePass {

  private var counter = 0

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (builder.parent.getInitProcedures().none { it.first == builder }) return builder
    val params = builder.getParams().filter { it.second != ParamDirection.OUT }.map { it.first }
    if (params.isEmpty()) return builder
    val used = builder.getEdges().flatMap { it.label.collectVars() }.toSet()
    if (params.drop(2).any { it in used }) {
      throw UnsupportedFrontendElementException("An entry point that reads its third parameter")
    }
    val argc = params[0]
    val argv = params.getOrNull(1)?.takeIf { it in used }
    if (argc !in used && argv == null) return builder
    val called =
      builder.parent.getProcedures().any { proc ->
        proc.getEdges().any { edge ->
          edge.getFlatLabels().any { it is InvokeLabel && it.name == builder.name }
        }
      }
    if (called) throw UnsupportedFrontendElementException("A call to the entry point")

    val argcType = CComplexType.getType(argc.ref, parseContext)
    val array = argv?.let { CComplexType.getType(it.ref, parseContext) }
    val element = (array as? CPointer)?.embeddedType ?: (array as? CArray)?.embeddedType
    val char = (element as? CPointer)?.embeddedType
    if (argcType !is CInteger || (argv != null && char !is CInteger)) {
      throw UnsupportedFrontendElementException(
        "Entry point parameters that are not `int argc, char *argv[]`"
      )
    }

    val labels = mutableListOf<XcfaLabel>(HavocStmtLabel(argc.ref))
    labels.addAll(withinTypeRange(argc.ref, parseContext, EmptyMetaData))
    labels.add(StmtLabel(Assume(Geq(argc.ref, argcType.nullValue))))
    // after the global initialization, which resets the memory-safety bookkeeping
    val initialization =
      builder.initLoc.outgoingEdges.singleOrNull()
        ?: error("The entry point does not start with one initialization edge")
    val body = initialization.target
    val start = location(builder)
    builder.removeEdge(initialization)
    builder.addEdge(initialization.withTarget(start))
    if (argv == null) {
      builder.addEdge(XcfaEdge(start, body, SequenceLabel(labels), EmptyMetaData))
      return builder
    }
    builder.parent.entryArguments.add(argv)

    val pointerBytes = (ObjectLayout.sizeBits(element, parseContext.architecture) / 8).toLong()
    val stride = if (parseContext.memoryModel.byteAddressed()) pointerBytes else 1L
    val maxBytes = BigInteger.ONE.shiftLeft((size as CInteger).width() - 1) - BigInteger.ONE
    val count = size.castTo(argc.ref)
    val maxCount = maxBytes / BigInteger.valueOf(pointerBytes) - BigInteger.ONE
    labels.add(StmtLabel(Assume(Leq(count, size.getValue("$maxCount")))))
    labels.add(
      InvokeLabel.retFirst(
        STATIC_OBJECT,
        listOf(argv.ref, Mul(Add(count, sizeOf(1)), sizeOf(stride))),
        EmptyMetaData,
      )
    )
    val strings = Strings(builder, element!!, char as CInteger, maxBytes)
    val terminate = AssignStmtLabel(cell(argv.ref, count, element, stride), element.nullValue)

    val indices = constantIndices(builder, argv, stride)
    if (indices != null) {
      // the strings of the indices below argc, in increasing order: the first index not below it
      // ends the list
      val end = location(builder)
      var at = location(builder)
      builder.addEdge(XcfaEdge(start, at, SequenceLabel(labels), EmptyMetaData))
      for (index in indices) {
        val next = location(builder)
        val constant = size.getValue("$index")
        strings.create(at, next, listOf(StmtLabel(Assume(Lt(constant, count))))) { string ->
          listOf(AssignStmtLabel(cell(argv.ref, constant, element, stride), string.ref))
        }
        builder.addEdge(
          XcfaEdge(
            at,
            end,
            SequenceLabel(listOf(StmtLabel(Assume(Geq(constant, count))))),
            EmptyMetaData,
          )
        )
        at = next
      }
      builder.addEdge(XcfaEdge(at, end, SequenceLabel(listOf(NopLabel)), EmptyMetaData))
      builder.addEdge(XcfaEdge(end, body, SequenceLabel(listOf(terminate)), EmptyMetaData))
      return builder
    }

    val i = fresh(builder, "i", size)
    labels.add(AssignStmtLabel(i, sizeOf(0)))
    val outer = location(builder)
    builder.addEdge(XcfaEdge(start, outer, SequenceLabel(labels), EmptyMetaData))
    val stored = location(builder)
    strings.create(outer, stored, listOf(StmtLabel(Assume(Lt(i.ref, count))))) { string ->
      listOf(
        AssignStmtLabel(cell(argv.ref, i.ref, element, stride), string.ref),
        AssignStmtLabel(i, Add(i.ref, sizeOf(1))),
      )
    }
    builder.addEdge(XcfaEdge(stored, outer, SequenceLabel(listOf(NopLabel)), EmptyMetaData))
    builder.addEdge(
      XcfaEdge(
        outer,
        body,
        SequenceLabel(listOf(StmtLabel(Assume(Geq(i.ref, count))), terminate)),
        EmptyMetaData,
      )
    )
    return builder
  }

  /** Creates the strings `argv` points to, each in a fresh static object. */
  private inner class Strings(
    val builder: XcfaProcedureBuilder,
    val element: CComplexType,
    val char: CInteger,
    val maxBytes: BigInteger,
  ) {
    /**
     * Edges from [from] to [to] that start with [pre], create a string and end with [post] of it.
     */
    fun create(
      from: XcfaLocation,
      to: XcfaLocation,
      pre: List<XcfaLabel>,
      post: (VarDecl<*>) -> List<XcfaLabel>,
    ) {
      val length = fresh(builder, "length", size)
      val string = fresh(builder, "string", element)
      val allocation =
        pre +
          HavocStmtLabel(length.ref) +
          withinTypeRange(length.ref, parseContext, EmptyMetaData) +
          listOf(
            StmtLabel(Assume(Geq(length.ref, sizeOf(1)))),
            StmtLabel(Assume(Leq(length.ref, size.getValue("$maxBytes")))),
            InvokeLabel.retFirst(STATIC_OBJECT, listOf(string.ref, length.ref), EmptyMetaData),
          )
      val last = Sub(length.ref, sizeOf(1))
      val terminated =
        listOf(AssignStmtLabel(cell(string.ref, last, char, 1L), char.nullValue)) + post(string)
      if (!parseContext.isCheckMemsafety) {
        builder.addEdge(XcfaEdge(from, to, SequenceLabel(allocation + terminated), EmptyMetaData))
        return
      }
      val j = fresh(builder, "j", size)
      val inner = location(builder)
      builder.addEdge(
        XcfaEdge(
          from,
          inner,
          SequenceLabel(allocation + AssignStmtLabel(j, sizeOf(0))),
          EmptyMetaData,
        )
      )
      val character = fresh(builder, "char", char)
      val stepped = location(builder)
      builder.addEdge(
        XcfaEdge(
          inner,
          stepped,
          SequenceLabel(
            listOf(StmtLabel(Assume(Lt(j.ref, last))), HavocStmtLabel(character.ref)) +
              withinTypeRange(character.ref, parseContext, EmptyMetaData) +
              listOf(
                StmtLabel(Assume(Neq(character.ref, char.nullValue))),
                AssignStmtLabel(cell(string.ref, j.ref, char, 1L), character.ref),
                AssignStmtLabel(j, Add(j.ref, sizeOf(1))),
              )
          ),
          EmptyMetaData,
        )
      )
      builder.addEdge(XcfaEdge(stepped, inner, SequenceLabel(listOf(NopLabel)), EmptyMetaData))
      builder.addEdge(
        XcfaEdge(
          inner,
          to,
          SequenceLabel(listOf(StmtLabel(Assume(Geq(j.ref, last)))) + terminated),
          EmptyMetaData,
        )
      )
    }
  }

  /**
   * The indices at which [builder] accesses [argv], in increasing order, if it uses it only as the
   * array of dereferences at constant offsets; null otherwise.
   */
  private fun constantIndices(
    builder: XcfaProcedureBuilder,
    argv: VarDecl<*>,
    stride: Long,
  ): List<BigInteger>? {
    val indices = sortedSetOf<BigInteger>()
    fun constantOnly(expr: Expr<*>): Boolean =
      if (expr is Dereference<*, *, *> && expr.array == argv.ref) {
        val offset = ExprUtils.simplify(expr.offset).asConstantBigInteger()
        val (index, rest) = offset?.divideAndRemainder(BigInteger.valueOf(stride)) ?: return false
        rest.signum() == 0 && index.signum() >= 0 && indices.add(index).let { true }
      } else expr != argv.ref && expr.ops.all(::constantOnly)
    fun constantOnly(label: XcfaLabel): Boolean =
      when (label) {
        is SequenceLabel -> label.labels.all(::constantOnly)
        is NondetLabel -> label.labels.all(::constantOnly)
        is InvokeLabel -> label.params.all(::constantOnly)
        is StartLabel -> label.pidVar != argv && label.params.all(::constantOnly)
        is JoinLabel -> label.pidVar != argv
        is FenceLabel -> argv !in label.collectVars()
        is StmtLabel ->
          when (val stmt = label.stmt) {
            is AssumeStmt -> constantOnly(stmt.cond)
            is AssignStmt<*> -> stmt.varDecl != argv && constantOnly(stmt.expr)
            is HavocStmt<*> -> stmt.varDecl != argv
            is MemoryAssignStmt<*, *, *> -> constantOnly(stmt.deref) && constantOnly(stmt.expr)
            else -> argv !in label.collectVars()
          }
        else -> argv !in label.collectVars()
      }
    return if (builder.getEdges().all { constantOnly(it.label) }) indices.toList() else null
  }

  private val size by lazy { CComplexType.getUnsignedLong(parseContext) }

  private fun sizeOf(value: Long) = size.getValue("$value")

  private fun cell(base: Expr<*>, index: Expr<*>, type: CComplexType, unit: Long): Expr<*> {
    val offset = if (unit == 1L) index else Mul(index, sizeOf(unit))
    return Dereference(cast(base, base.type), cast(offset, base.type), type.smtType).also {
      parseContext.metadata.create(it, "cType", type)
    }
  }

  private fun location(builder: XcfaProcedureBuilder) =
    XcfaLocation("${builder.name}_arguments_${counter++}", metadata = EmptyMetaData)
      .also(builder::addLoc)

  private fun fresh(
    builder: XcfaProcedureBuilder,
    name: String,
    type: CComplexType,
  ): VarDecl<Type> =
    Decls.Var("__theta_argv_${name}_${counter++}", type.smtType).also {
      parseContext.metadata.create(it.ref, "cType", type)
      builder.addVar(it)
    }
}
