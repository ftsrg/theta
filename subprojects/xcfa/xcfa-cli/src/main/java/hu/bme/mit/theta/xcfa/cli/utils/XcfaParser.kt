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
package hu.bme.mit.theta.xcfa.cli.utils

import com.charleskorn.kaml.*
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Lexer
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser
import hu.bme.mit.theta.btor2xcfa.Btor2XcfaBuilder
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.cfa.dsl.CfaDslManager
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.RequiresByteAddressedMemoryException
import hu.bme.mit.theta.frontend.chc.ChcFrontend
import hu.bme.mit.theta.frontend.litmus2xcfa.LitmusInterpreter
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.frontend.visitors.Btor2Visitor
import hu.bme.mit.theta.llvm2xcfa.ArithmeticType
import hu.bme.mit.theta.llvm2xcfa.XcfaUtils
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ChcPasses
import hu.bme.mit.theta.xcfa.passes.DereferenceToArrayPass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import hu.bme.mit.theta.xcfa.passes.UnsupportedPointerSplitException
import java.io.File
import java.io.FileInputStream
import java.io.FileReader
import java.util.concurrent.TimeUnit
import javax.script.ScriptEngine
import javax.script.ScriptEngineManager
import kotlin.io.path.createTempDirectory
import kotlin.jvm.optionals.getOrNull
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

/**
 * Builds the XCFA for the configured input.
 *
 * Failures here do not propagate: they are logged and the process exits, so a caller cannot simply
 * wrap this in a `try`. The two failure modes a caller CAN recover from are therefore handed back
 * untouched when it asks for them, and only then:
 * - [rethrowPointerSplitLimitation]: the base/offset pointer splitting of `--memory-model multi`
 *   giving up ([UnsupportedPointerSplitException]), recoverable under `--memory-model flat` (and
 *   then under `--memory-model bytes` if flat needs byte granularity).
 * - [rethrowByteGranularityLimitation]: a construct that needs byte granularity
 *   ([RequiresByteAddressedMemoryException]), recoverable under `--memory-model bytes`.
 *
 * Every other failure is reported and exits as before.
 */
fun getXcfa(
  config: XcfaConfig<*, *>,
  parseContext: ParseContext,
  logger: Logger,
  uniqueWarningLogger: Logger,
  rethrowPointerSplitLimitation: Boolean = false,
  rethrowByteGranularityLimitation: Boolean = false,
) =
  try {
    when (config.frontendConfig.inputType) {
      InputType.CHC -> {
        val chcConfig = config.frontendConfig.specConfig as CHCFrontendConfig
        parseChc(
          config.inputConfig.input!!,
          chcConfig.chcTransformation,
          parseContext,
          logger,
          uniqueWarningLogger,
        )
      }

      InputType.C -> {
        parseC(
          config.frontendConfig.specConfig as CFrontendConfig,
          config.inputConfig.input!!,
          config.inputConfig.property,
          parseContext,
          logger,
          uniqueWarningLogger,
          config.outputConfig.resultFolder,
        ) { client ->
          // The witness describes the generated client program, not the library input.
          val witness = config.outputConfig.witnessConfig
          if (witness.inputFileForWitness == null) witness.inputFileForWitness = client
        }
      }

      InputType.LLVM -> XcfaUtils.fromFile(config.inputConfig.input!!, ArithmeticType.efficient)

      InputType.LITMUS -> LitmusInterpreter.getXcfa(config.inputConfig.input!!)

      InputType.DSL -> {
        val kotlinEngine: ScriptEngine = ScriptEngineManager().getEngineByExtension("kts")
        kotlinEngine.eval(FileReader(config.inputConfig.input!!)) as XCFA
      }

      InputType.CFA -> {
        FileInputStream(config.inputConfig.input!!).use { inputStream ->
          try {
            return CfaDslManager.createCfa(inputStream).toXcfa()
          } catch (ex: java.lang.Exception) {
            throw java.lang.Exception("Could not parse CFA: " + ex.message, ex)
          }
        }
      }

      InputType.BTOR2 -> {
        val btor2Frontend = config.frontendConfig.specConfig as BTOR2FrontendConfig
        parseBTOR2(
          config.inputConfig.input!!,
          btor2Frontend.btor2Passes,
          parseContext,
          logger,
          uniqueWarningLogger,
        )
      }
    }
  } catch (e: Exception) {
    // Give the caller its chance to retry under a memory model that has no pointer splitting at
    // all, before anything is logged as a failure -- this build attempt is not the last word.
    if (rethrowPointerSplitLimitation) {
      e.pointerSplitLimitation()?.let { throw it }
    }
    if (rethrowByteGranularityLimitation) {
      e.byteGranularityLimitation()?.let { throw it }
    }
    if (config.debugConfig.stacktrace) e.printStackTrace()
    val location =
      e.stackTrace.filter { it.className.startsWith("hu.bme.mit.theta") }.first().toString()
    logger.write(Logger.Level.RESULT, "%s", "Frontend failed! ($location, $e)\n")
    exitProcess(config.debugConfig.debug, e, ExitCodes.FRONTEND_FAILED.code)
  }

/**
 * The [UnsupportedPointerSplitException] in this throwable's cause chain, or null if the failure is
 * something else entirely. The chain has to be walked because the frontend wraps failures on its
 * way out (e.g. the retry-with-bitvector-arithmetic path in [parseC]).
 */
private fun Throwable.pointerSplitLimitation(): UnsupportedPointerSplitException? {
  val seen = mutableSetOf<Throwable>()
  var current: Throwable? = this
  while (current != null && seen.add(current)) {
    if (current is UnsupportedPointerSplitException) return current
    current = current.cause
  }
  return null
}

/**
 * The [RequiresByteAddressedMemoryException] in this throwable's cause chain, or null if the
 * failure is something else. Walked for the same reason as [pointerSplitLimitation]: the frontend
 * wraps failures on their way out.
 */
private fun Throwable.byteGranularityLimitation(): RequiresByteAddressedMemoryException? {
  val seen = mutableSetOf<Throwable>()
  var current: Throwable? = this
  while (current != null && seen.add(current)) {
    if (current is RequiresByteAddressedMemoryException) return current
    current = current.cause
  }
  return null
}

private fun CFA.toXcfa(): XCFA {
  val xcfaBuilder = XcfaBuilder("chc")
  val builder = XcfaProcedureBuilder("main", ProcedurePassManager())
  this.vars.forEach(builder::addVar)

  builder.createInitLoc()
  builder.createErrorLoc()
  builder.createFinalLoc()

  val initLocation = builder.initLoc
  val errorLocation = builder.errorLoc.get()
  val finalLocation = builder.finalLoc.get()

  val locs =
    locs.associateWith {
      when {
        this.initLoc == it -> initLocation
        this.finalLoc.getOrNull() == it -> finalLocation
        this.errorLoc.getOrNull() == it -> errorLocation
        else -> XcfaLocation(it.name, metadata = EmptyMetaData).also { builder.addLoc(it) }
      }
    }
  edges.forEach {
    XcfaEdge(
        locs[it.source]!!,
        locs[it.target]!!,
        StmtLabel(stmt = it.stmt, metadata = EmptyMetaData),
        metadata = EmptyMetaData,
      )
      .apply { builder.addEdge(this) }
  }

  xcfaBuilder.addProcedure(builder)
  xcfaBuilder.addEntryPoint(builder, ArrayList())
  return xcfaBuilder.build()
}

/**
 * Lowers the inputs to C with Cir2C: a single file, one file per translation unit for the multi-TU
 * frontend to link, or with `--cir2c-merge` one file made by cir-merge for the regular frontend.
 */
private fun runCir2c(inputs: List<File>, config: CFrontendConfig, logger: Logger): List<File> {
  val temp = createTempDirectory().toFile()
  // The input is copied, so what it includes relative to itself has to be found another way.
  fun includes(file: File) = listOf("--cflag", "-I${file.absoluteFile.parent}")
  val userArgs = config.cir2cArgs.trim().split(Regex("\\s+")).filter { it.isNotEmpty() }
  val copies =
    inputs.mapIndexed { i, inputFile ->
      val copied = temp.resolve("tu$i").also { it.mkdirs() }.resolve(inputFile.name)
      var curlyBraceCount = 0
      inputFile.readLines().forEach { line ->
        line.forEach { c -> if (c == '{') curlyBraceCount++ else if (c == '}') curlyBraceCount-- }
        val newLine =
          if (curlyBraceCount == 0 && '{' !in line) {
            "([^(]*)\\(\\s*\\)".toRegex().replace(line) { it.groups[1]!!.value + "(void)" }
          } else {
            line
          }
        copied.appendText(newLine)
        copied.appendText(System.lineSeparator())
      }
      copied
    }
  // run-cir2c.sh drives the whole Cir2C pipeline (clang -emit-cir -> preprocess -> cir2c) and finds
  // its own toolchain relative to the script.
  val script = "./run-cir2c.sh"
  if (inputs.size == 1 || config.cir2cMerge) {
    val transformed = temp.resolve("input-transformed.c")
    val merge = if (inputs.size > 1) listOf("--merge", "cir") else emptyList()
    val args =
      listOf(script) +
        merge +
        inputs.distinctBy { it.absoluteFile.parent }.flatMap(::includes) +
        userArgs +
        copies.map { it.absolutePath } +
        transformed.absolutePath
    args.runCommand(config.cir2cDir, logger)
    return listOf(transformed)
  }
  return copies.indices
    .toList()
    .parallelStream()
    .map { i ->
      val transformed = temp.resolve("tu$i-transformed.c")
      val args =
        listOf(script, "--tu-part") +
          includes(inputs[i]) +
          userArgs +
          copies[i].absolutePath +
          transformed.absolutePath
      args.runCommand(config.cir2cDir, logger)
      transformed
    }
    .toList()
}

/**
 * The single C input with the most general client of [api] as its `main` (see [LibraryClient]),
 * written to [dir] (the result folder) so that a counterexample can be read as client code.
 */
private fun withLibraryClient(inputs: List<File>, api: File, dir: File, logger: Logger): File {
  check(inputs.size == 1) { "--library needs a single C input (merge the units first)" }
  val input = inputs.single()
  val source =
    LibraryClient(
        input.readText(),
        LibraryApi.parse(api.readText()),
        DereferenceToArrayPass.zeroInitialized,
      )
      .source()
  dir.mkdirs()
  val out = File(dir, input.nameWithoutExtension + ".library.c").absoluteFile
  out.writeText(source)
  logger.result("%s", "Verifying ${input.name} as a library against any client: ${out.path}\n")
  return out
}

private fun parseC(
  frontendConfig: CFrontendConfig,
  input: File,
  property: XcfaProperty,
  parseContext: ParseContext,
  logger: Logger,
  uniqueWarningLogger: Logger,
  libraryClientDir: File = File("."),
  onLibraryClient: (File) -> Unit = {},
): XCFA {
  // Resolve input file(s) from .yml manifest or direct file
  val inputs: List<File> =
    if (input.name.endsWith(".yml")) {
      try {
        val parsedYaml = Yaml.default.parseToYamlNode(input.readText())
        if (parsedYaml is YamlMap) {
          when (val files = parsedYaml.get<YamlNode>("input_files")) {
            is YamlList -> {
              val resolved =
                files.items.map {
                  input.absoluteFile.parentFile.resolve((it as YamlScalar).content)
                }
              logger.result(
                "%s",
                "Parsing ${resolved.size} input file(s) from ${input.name}: " +
                  resolved.joinToString(" ") { it.name },
              )
              resolved
            }
            is YamlScalar -> {
              val inputFile = input.absoluteFile.parentFile.resolve(files.content)
              logger.result("%s", "Parsing ${inputFile.name} instead of ${input.name}")
              listOf(inputFile)
            }
            else -> {
              logger.info("%s", "Unexpected yml content: $files")
              listOf(input)
            }
          }
        } else {
          logger.info("%s", "Unexpected yml content: $parsedYaml")
          listOf(input)
        }
      } catch (ex: Exception) {
        logger.info("%s", "Could not parse YAML data: ${ex.message}")
        listOf(input)
      }
    } else {
      listOf(input)
    }

  val translatedInputs =
    if (frontendConfig.useCir2c) runCir2c(inputs, frontendConfig, logger) else inputs
  val transformedInputs =
    frontendConfig.library?.let { api ->
      listOf(
        withLibraryClient(translatedInputs, api, libraryClientDir, logger).also(onLibraryClient)
      )
    } ?: translatedInputs

  // Parse single or multiple translation units
  val xcfaFromC =
    try {
      if (transformedInputs.size == 1) {
        val stream = FileInputStream(transformedInputs[0])
        getXcfaFromC(stream, parseContext, false, property, uniqueWarningLogger, logger).first
      } else {
        getXcfaFromC(transformedInputs, parseContext, false, property, uniqueWarningLogger, logger)
          .first
      }
    } catch (e: Throwable) {
      // The retry used to require `efficient`, which it never saw: FunctionVisitor resolves
      // `efficient` into integer or bitvector before the parse gets far enough to fail, so by the
      // time an exception arrives the arithmetic always reads as an explicit choice. The fallback
      // was therefore dead for exactly the programs it was written for -- one whose bit
      // manipulation the checker missed would fail with "only modelled over bitvectors" and never
      // be retried. An automatically chosen encoding may be revised; an explicitly requested one
      // may not.
      val revisable =
        parseContext.arithmetic == ArchitectureConfig.ArithmeticType.efficient ||
          (parseContext.isArithmeticAutoSelected &&
            parseContext.arithmetic != ArchitectureConfig.ArithmeticType.bitvector)
      if (revisable) {
        parseContext.arithmetic = ArchitectureConfig.ArithmeticType.bitvector
        logger.write(Logger.Level.INFO, "Retrying parsing with bitvector arithmetic...\n")
        val xcfa =
          if (transformedInputs.size == 1) {
            val stream = FileInputStream(transformedInputs[0])
            getXcfaFromC(stream, parseContext, false, property, uniqueWarningLogger, logger).first
          } else {
            getXcfaFromC(
                transformedInputs,
                parseContext,
                false,
                property,
                uniqueWarningLogger,
                logger,
              )
              .first
          }
        parseContext.addArithmeticTrait(ArithmeticTrait.BITWISE)
        xcfa
      } else {
        throw e
      }
    }
  logger.benchmark("%s", "Arithmetic: ${parseContext.arithmeticTraits}\n")
  return xcfaFromC
}

private fun parseChc(
  input: File,
  chcTransformation: ChcFrontend.ChcTransformation,
  parseContext: ParseContext,
  logger: Logger,
  uniqueWarningLogger: Logger,
): XCFA {
  var chcFrontend: ChcFrontend
  val xcfaBuilder =
    if (
      chcTransformation == ChcFrontend.ChcTransformation.PORTFOLIO
    ) { // try forward, fallback to backward
      chcFrontend = ChcFrontend(ChcFrontend.ChcTransformation.FORWARD)
      try {
        chcFrontend.buildXcfa(
          CharStreams.fromStream(FileInputStream(input)),
          ChcPasses(parseContext, uniqueWarningLogger),
        )
      } catch (e: UnsupportedOperationException) {
        logger.write(
          Logger.Level.INFO,
          "Non-linear CHC found, retrying using backward transformation...\n",
        )
        chcFrontend = ChcFrontend(ChcFrontend.ChcTransformation.BACKWARD)
        chcFrontend.buildXcfa(
          CharStreams.fromStream(FileInputStream(input)),
          ChcPasses(parseContext, uniqueWarningLogger),
        )
      }
    } else {
      chcFrontend = ChcFrontend(chcTransformation)
      chcFrontend.buildXcfa(
        CharStreams.fromStream(FileInputStream(input)),
        ChcPasses(parseContext, uniqueWarningLogger),
      )
    }
  return xcfaBuilder.build()
}

private fun parseBTOR2(
  input: File,
  btor2Passes: Boolean,
  parseContext: ParseContext,
  logger: Logger,
  uniqueLogger: Logger,
): XCFA {
  val visitor = Btor2Visitor(logger)

  val inputBTOR2 = input.readLines().joinToString("\n")
  val cinput = CharStreams.fromString(inputBTOR2)
  val lexer = Btor2Lexer(cinput)
  val tokens = CommonTokenStream(lexer)
  val parser = Btor2Parser(tokens)
  parser.errorHandler = BailErrorStrategy()
  val context = parser.btor2()

  context.accept(visitor)

  val xcfa = Btor2XcfaBuilder().btor2xcfa(visitor.circuit, btor2Passes, parseContext, uniqueLogger)
  logger.write(Logger.Level.VERBOSE, "%s", xcfa.toDot())
  return xcfa
}

private fun List<String>.runCommand(
  wd: File,
  logger: Logger,
  level: Logger.Level = Logger.Level.INFO,
) {
  val process = ProcessBuilder(this).directory(wd).redirectErrorStream(true).start()
  process.inputStream.bufferedReader().useLines { lines ->
    lines.forEach { logger.write(level, "%s%n", it) }
  }
  check(process.waitFor(15, TimeUnit.MINUTES)) { "Timed out: ${joinToString(" ")}" }
  check(process.exitValue() == 0) { "Exit code ${process.exitValue()}: ${joinToString(" ")}" }
}
