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

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.asConstantBigInteger
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Decides what a stubbed formatted call accesses, for the memory-safety properties only. Which
 * argument a `%s` takes is known once the format has its literal, so [LibraryStubsPass] leaves
 * markers and this pass, after inlining, turns them into [STRING_READ] and [BOUNDED_WRITE] calls
 * that [MemoryFunctionsPass] lowers ahead of the guards. A format of unknown text checks nothing,
 * and a string literal needs no check.
 *
 * A string read touches only the first character, as a loop per printed string is costly. It misses
 * an unterminated string, but invents nothing. A marker names its format by an id in
 * [XcfaBuilder.formatMarkers]: constant folding replaces the expression before this pass runs.
 */
class FormatAccessPass(val parseContext: ParseContext) : ProcedurePass {

  companion object {
    /** `(format id, arguments...)`: a call that reads its `%s` arguments. */
    const val FORMAT_READS = "__theta_format_reads"

    /** `(format id, destination, arguments...)`: `sprintf` into the destination. */
    const val FORMAT_WRITE = "__theta_format_write"

    /** `(format id, destination, size, arguments...)`: `snprintf` into the destination. */
    const val FORMAT_WRITE_BOUNDED = "__theta_format_write_bounded"

    /** `(string)`: a call that reads a string, whatever its format. */
    const val PLAIN_STRING_READ = "__theta_plain_string_read"

    /** `(string)`: reads the first character of the string. */
    const val STRING_READ = "__theta_string_read"

    /** `(destination, literal length, source, size?)`: writes a format of one plain `%s`. */
    const val BOUNDED_WRITE = "__theta_bounded_write"
  }

  private var analysis: PrintfReturnBoundPass.Literals? = null

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!parseContext.isCheckMemsafety) return builder
    val literals = analysis ?: PrintfReturnBoundPass.Literals(builder.parent).also { analysis = it }
    val markers = setOf(FORMAT_READS, FORMAT_WRITE, FORMAT_WRITE_BOUNDED, PLAIN_STRING_READ)
    for (edge in ArrayList(builder.getEdges())) {
      val labels = edge.getFlatLabels()
      if (labels.none { it is InvokeLabel && it.name in markers }) continue
      val resolved =
        labels.flatMap { label ->
          when ((label as? InvokeLabel)?.name) {
            FORMAT_READS -> reads(label, literals, builder)
            FORMAT_WRITE -> write(label, null, literals, builder)
            FORMAT_WRITE_BOUNDED -> write(label, label.params[2], literals, builder)
            PLAIN_STRING_READ -> stringRead(label.params[0], literals, label)
            else -> listOf(label)
          }
        }
      builder.removeEdge(edge)
      builder.addEdge(edge.withLabel(SequenceLabel(resolved, edge.label.metadata)))
    }
    return builder
  }

  private fun PrintfReturnBoundPass.Literals.texts(
    invoke: InvokeLabel,
    builder: XcfaProcedureBuilder,
  ): List<String>? {
    val id = invoke.params[0].asConstantBigInteger()?.toInt() ?: return null
    return builder.parent.formatMarkers[id]?.let { textsOf(it) }
  }

  private fun reads(
    invoke: InvokeLabel,
    literals: PrintfReturnBoundPass.Literals,
    builder: XcfaProcedureBuilder,
  ): List<XcfaLabel> {
    val texts = literals.texts(invoke, builder) ?: return listOf()
    val conversions = texts.map { stringArguments(it) ?: return listOf() }.distinct()
    val common = conversions.singleOrNull() ?: return listOf()
    return common.flatMap { position ->
      invoke.params.getOrNull(position + 1)?.let { stringRead(it, literals, invoke) } ?: listOf()
    }
  }

  private fun stringRead(
    string: Expr<*>,
    literals: PrintfReturnBoundPass.Literals,
    invoke: InvokeLabel,
  ): List<XcfaLabel> =
    if (literals.isLiteralBase(string)) listOf()
    else listOf(InvokeLabel(STRING_READ, listOf(string), metadata = invoke.metadata))

  /** The source is walked, so its cells must be exact: this has to be the only buffer stub. */
  private fun write(
    invoke: InvokeLabel,
    size: Expr<*>?,
    literals: PrintfReturnBoundPass.Literals,
    builder: XcfaProcedureBuilder,
  ): List<XcfaLabel> {
    if (builder.parent.bufferStubCalls != 1) return listOf()
    val text = literals.texts(invoke, builder)?.singleOrNull() ?: return listOf()
    val literalLength = plainStringFormat(text) ?: return listOf()
    val first = if (size == null) 2 else 3
    if (invoke.params.size != first + 1) return listOf()
    val length = CComplexType.getUnsignedLong(parseContext).getValue("$literalLength")
    return listOf(
      InvokeLabel(
        BOUNDED_WRITE,
        listOfNotNull(invoke.params[1], length, invoke.params[first], size),
        metadata = invoke.metadata,
      )
    )
  }
}

/**
 * The positions among the variadic arguments of the plain `%s` conversions that read a character,
 * or null for a conversion this does not parse. A `*` takes an argument of its own, and a wide
 * `%ls` is not a `char` string.
 */
internal fun stringArguments(format: String): List<Int>? {
  val strings = mutableListOf<Int>()
  var argument = 0
  var i = 0
  while (i < format.length) {
    if (format[i++] != '%') continue
    if (i < format.length && format[i] == '%') {
      i++
      continue
    }
    while (i < format.length && format[i] in "-+ #0") i++
    if (i < format.length && format[i] == '*') {
      argument++
      i++
    } else while (i < format.length && format[i].isDigit()) i++
    var readsCharacter = true
    if (i < format.length && format[i] == '.') {
      i++
      if (i < format.length && format[i] == '*') {
        argument++
        i++
        readsCharacter = false
      } else {
        val start = i
        while (i < format.length && format[i].isDigit()) i++
        readsCharacter = format.substring(start, i).any { it != '0' }
      }
    }
    val modified = i < format.length && format[i] in "hljztL"
    while (i < format.length && format[i] in "hljztL") i++
    if (i >= format.length || format[i] !in "diouxXeEfFgGaAcspn") return null
    if (format[i] == 's' && !modified && readsCharacter) strings.add(argument)
    argument++
    i++
  }
  return strings
}

/** The characters [format] writes besides its one plain `%s`, or null for any other format. */
internal fun plainStringFormat(format: String): Long? {
  var literal = 0L
  var strings = 0
  var i = 0
  while (i < format.length) {
    if (format[i] != '%') {
      literal++
      i++
      continue
    }
    when (format.getOrNull(i + 1)) {
      '%' -> literal++
      's' -> strings++
      else -> return null
    }
    i += 2
  }
  return if (strings == 1) literal else null
}
