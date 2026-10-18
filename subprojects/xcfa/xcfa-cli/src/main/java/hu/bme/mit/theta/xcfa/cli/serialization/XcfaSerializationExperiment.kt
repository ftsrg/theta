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
package hu.bme.mit.theta.xcfa.cli.serialization

import com.beust.jcommander.JCommander
import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.common.logging.UniqueWarningLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.cli.buildXcfaForExperiment
import hu.bme.mit.theta.xcfa.cli.params.SpecBackendConfig
import hu.bme.mit.theta.xcfa.cli.params.SpecFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.ReturnLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.serialization.XcfaSerialization
import java.io.File
import java.lang.management.ManagementFactory
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.cbor.Cbor
import kotlinx.serialization.json.Json
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.modules.polymorphic
import kotlinx.serialization.protobuf.ProtoBuf

/**
 * Measures whether a built XCFA can be handed to a worker process faster than the worker could
 * re-parse the input.
 *
 * `measure <outDir> <theta args>`: parses (cold, as a worker would), then per format encodes,
 * writes, decodes, checks the round trip and times warm encode/decode.
 *
 * `load <file> [theta args]`: in a fresh JVM, reads and decodes a written file; with theta args it
 * then runs that configuration on the decoded XCFA instead of parsing the input.
 */
@OptIn(ExperimentalSerializationApi::class)
object XcfaSerializationExperiment {

  private val module =
    XcfaSerialization.module(
      SerializersModule {
        polymorphic(MetaData::class) { subclass(CMetaData::class, CMetaData.serializer()) }
      }
    )

  enum class Format(val extension: String) {
    JSON("json"),
    PROTOBUF("pb"),
    CBOR("cbor");

    // The default discriminator "type" clashes with surrogate properties of that name.
    private val json by lazy {
      Json {
        serializersModule = module
        classDiscriminator = "#class"
      }
    }
    private val protoBuf by lazy { ProtoBuf { serializersModule = module } }
    private val cbor by lazy { Cbor { serializersModule = module } }

    fun encode(xcfa: XCFA, parseContext: ParseContext): ByteArray =
      when (this) {
        JSON -> XcfaSerialization.encodeToString(json, xcfa, parseContext).encodeToByteArray()
        PROTOBUF -> XcfaSerialization.encodeToByteArray(protoBuf, xcfa, parseContext)
        CBOR -> XcfaSerialization.encodeToByteArray(cbor, xcfa, parseContext)
      }

    fun decode(bytes: ByteArray): Pair<XCFA, ParseContext> =
      when (this) {
        JSON -> XcfaSerialization.decodeFromString(json, bytes.decodeToString())
        PROTOBUF -> XcfaSerialization.decodeFromByteArray(protoBuf, bytes)
        CBOR -> XcfaSerialization.decodeFromByteArray(cbor, bytes)
      }
  }

  private fun ms(nanos: Long) = "%.1f".format(nanos / 1e6)

  private fun uptime() = ManagementFactory.getRuntimeMXBean().uptime

  private inline fun <T> timed(block: () -> T): Pair<T, Long> {
    val start = System.nanoTime()
    val result = block()
    return result to System.nanoTime() - start
  }

  private fun parseConfig(args: List<String>): XcfaConfig<*, *> {
    val config = XcfaConfig<SpecFrontendConfig, SpecBackendConfig>()
    val remaining = ArrayList(args)
    while (remaining.isNotEmpty()) {
      val holder =
        object {
          @com.beust.jcommander.Parameter var rest: MutableList<String> = ArrayList()
        }
      val builder = JCommander.newBuilder().addObject(holder)
      config.getObjects().forEach { builder.addObject(it) }
      builder.build().parse(*remaining.toTypedArray())
      remaining.clear()
      remaining.addAll(holder.rest)
      if (!config.update() && remaining.isNotEmpty()) error("Extraneous parameters: $remaining")
    }
    return config
  }

  private fun shape(xcfa: XCFA) =
    "procedures=${xcfa.procedures.size} locs=${xcfa.procedures.sumOf { it.locs.size }} " +
      "edges=${xcfa.procedures.sumOf { it.edges.size }}"

  // astNodes are @Transient (not serialized), so they are left out of the comparison.
  private fun md(m: MetaData) = if (m is CMetaData) m.copy(astNodes = emptyList()) else m

  private fun labelDump(l: XcfaLabel): String =
    when (l) {
      is SequenceLabel -> "Seq@${md(l.metadata)}[${l.labels.joinToString { labelDump(it) }}]"
      is NondetLabel -> "Nondet@${md(l.metadata)}[${l.labels.joinToString { labelDump(it) }}]"
      is ReturnLabel -> "Return[${labelDump(l.enclosedLabel)}]"
      else -> "${l.javaClass.simpleName}($l)@${md(l.metadata)}"
    }

  private fun edgeDump(xcfa: XCFA): List<String> =
    xcfa.procedures.flatMap { p ->
      listOf("proc ${p.name} ${p.params} ${p.vars} init=${p.initLoc.name} prop=${p.prop}") +
        p.locs.map { "loc $it ${md(it.metadata)}" } +
        p.edges.map {
          "${it.source.name} -> ${it.target.name} : ${labelDump(it.label)} @ ${md(it.metadata)}"
        }
    } +
      xcfa.globalVars.map { "global $it" } +
      xcfa.initProcedures.map { "init ${it.first.name} ${it.second}" }

  private fun measure(outDir: File, thetaArgs: List<String>) {
    val config = parseConfig(thetaArgs)
    val logger: Logger = NullLogger.getInstance()
    val input = config.inputConfig.input!!
    val jvmStart = uptime()

    val (built, frontendNs) =
      timed { buildXcfaForExperiment(config, logger, UniqueWarningLogger(logger)) }
    val (xcfa, _, parseContext) = built
    println(
      "FRONTEND\t${input.path}\tsize=${input.length()}\t${shape(xcfa)}\t" +
        "frontend=${ms(frontendNs)}ms\tjvmStartMs=$jvmStart"
    )
    outDir.mkdirs()
    val dump = edgeDump(xcfa)

    for (format in Format.entries) {
      try {
        val (bytes, encodeNs) = timed { format.encode(xcfa, parseContext) }
        File(outDir, "${input.name}.${format.extension}").writeBytes(bytes)
        val (decoded, decodeNs) = timed { format.decode(bytes) }
        val reencoded = format.encode(decoded.first, decoded.second)
        val dump2 = edgeDump(decoded.first)
        println(
          "FORMAT\t${input.path}\t$format\tbytes=${bytes.size}\tencode=${ms(encodeNs)}ms\t" +
            "decode=${ms(decodeNs)}ms\treencodeEqual=${reencoded.contentEquals(bytes)}\t" +
            "dumpEqual=${dump == dump2}"
        )
        dump
          .zip(dump2)
          .firstOrNull { it.first != it.second }
          ?.let { println("FIRST-DIFF\n  ${it.first.take(500)}\n  ${it.second.take(500)}") }
        val warmEncode = ArrayList<Long>()
        val warmDecode = ArrayList<Long>()
        repeat(5) {
          warmEncode.add(timed { format.encode(xcfa, parseContext) }.second)
          warmDecode.add(timed { format.decode(bytes) }.second)
        }
        println(
          "WARM\t${input.path}\t$format\twarmEncode=${ms(warmEncode.sorted()[2])}ms\t" +
            "warmDecode=${ms(warmDecode.sorted()[2])}ms"
        )
      } catch (e: Throwable) {
        println("STAGE-FAILED\t${input.path}\t$format\t$e")
        e.stackTrace.take(12).forEach { println("    at $it") }
      }
    }
  }

  private fun load(file: File, thetaArgs: List<String>) {
    val format = Format.entries.first { file.name.endsWith(".${it.extension}") }
    val jvmStart = uptime()
    val (bytes, readNs) = timed { file.readBytes() }
    val (decoded, decodeNs) = timed { format.decode(bytes) }
    println(
      "LOAD\t${file.path}\t$format\tread=${ms(readNs)}ms\tdecode=${ms(decodeNs)}ms\t" +
        "total=${ms(readNs + decodeNs)}ms\t${shape(decoded.first)}\tjvmStartMs=$jvmStart"
    )
    if (thetaArgs.isNotEmpty()) {
      val config = parseConfig(thetaArgs)
      config.inputConfig.xcfaWCtx = Triple(decoded.first, emptySet(), decoded.second)
      val logger = ConsoleLogger(config.debugConfig.logLevel)
      runConfig(config, logger, UniqueWarningLogger(logger), false)
    }
  }

  @JvmStatic
  fun main(args: Array<String>) {
    when (args[0]) {
      "measure" -> measure(File(args[1]), args.drop(2))
      "load" -> load(File(args[1]), args.drop(2))
      "reencode" -> {
        val file = File(args[1])
        val format = Format.entries.first { file.name.endsWith(".${it.extension}") }
        val (xcfa, parseContext) = format.decode(file.readBytes())
        File(args[2]).writeBytes(format.encode(xcfa, parseContext))
      }
      else -> error("Unknown mode ${args[0]}")
    }
  }
}
