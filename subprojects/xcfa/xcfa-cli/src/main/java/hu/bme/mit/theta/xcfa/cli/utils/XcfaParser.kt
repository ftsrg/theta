/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Lexer
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser
import hu.bme.mit.theta.btor2xcfa.Btor2XcfaBuilder
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.cfa.dsl.CfaDslManager
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.chc.ChcFrontend
import hu.bme.mit.theta.frontend.litmus2xcfa.LitmusInterpreter
import hu.bme.mit.theta.frontend.models.Btor2Circuit
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.frontend.visitors.Btor2Visitor
import hu.bme.mit.theta.llvm2xcfa.ArithmeticType
import hu.bme.mit.theta.llvm2xcfa.XcfaUtils
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.cli.params.CHCFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.ExitCodes
import hu.bme.mit.theta.xcfa.cli.params.InputType
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ChcPasses
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import org.antlr.v4.runtime.BailErrorStrategy
import java.io.File
import java.io.FileInputStream
import java.io.FileReader
import javax.script.ScriptEngine
import javax.script.ScriptEngineManager
import kotlin.jvm.optionals.getOrNull
import kotlin.system.exitProcess
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

fun getXcfa(
  config: XcfaConfig<*, *>,
  parseContext: ParseContext,
  logger: Logger,
  uniqueWarningLogger: Logger,
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
          config.inputConfig.input!!,
          config.inputConfig.property,
          parseContext,
          logger,
          uniqueWarningLogger,
        )
      }

      InputType.LLVM -> XcfaUtils.fromFile(config.inputConfig.input!!, ArithmeticType.efficient)

      InputType.LITMUS -> LitmusInterpreter.getXcfa(config.inputConfig.input!!)

      InputType.JSON -> {
        val gson = getGson()
        gson.fromJson(config.inputConfig.input!!.readText(), XCFA::class.java)
      }

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
        parseBTOR2(
            config.inputConfig.input!!,
            logger,
            uniqueWarningLogger,
        )
      }
    }
  } catch (e: Exception) {
    if (config.debugConfig.stacktrace) e.printStackTrace()
    val location =
      e.stackTrace.filter { it.className.startsWith("hu.bme.mit.theta") }.first().toString()
    logger.write(Logger.Level.RESULT, "Frontend failed! ($location, $e)\n")
    exitProcess(ExitCodes.FRONTEND_FAILED.code)
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

private fun parseC(
  input: File,
  explicitProperty: ErrorDetection,
  parseContext: ParseContext,
  logger: Logger,
  uniqueWarningLogger: Logger,
): XCFA {
  val xcfaFromC =
    try {
      val stream = FileInputStream(input)
      getXcfaFromC(
          stream,
          parseContext,
          false,
          explicitProperty == ErrorDetection.OVERFLOW,
          uniqueWarningLogger,
        )
        .first
    } catch (e: Throwable) {
      if (parseContext.arithmetic == ArchitectureConfig.ArithmeticType.efficient) {
        parseContext.arithmetic = ArchitectureConfig.ArithmeticType.bitvector
        logger.write(Logger.Level.INFO, "Retrying parsing with bitvector arithmetic...\n")
        val stream = FileInputStream(input)
        val xcfa =
          getXcfaFromC(
              stream,
              parseContext,
              false,
              explicitProperty == ErrorDetection.OVERFLOW,
              uniqueWarningLogger,
            )
            .first
        parseContext.addArithmeticTrait(ArithmeticTrait.BITWISE)
        xcfa
      } else {
        throw e
      }
    }
  logger.write(Logger.Level.RESULT, "Arithmetic: ${parseContext.arithmeticTraits}\n")
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
    logger: Logger,
    uniqueWarningLogger: Logger
) : XCFA {
  val visitor = Btor2Visitor()
  val btor2File = input

  val input = btor2File.readLines().joinToString("\n")
  val cinput = CharStreams.fromString(input)
  val lexer = Btor2Lexer(cinput)
  val tokens = CommonTokenStream(lexer)
  val parser = Btor2Parser(tokens)
  parser.errorHandler = BailErrorStrategy()
  val context = parser.btor2()

  context.accept(visitor)

  val xcfa = Btor2XcfaBuilder.btor2xcfa(Btor2Circuit)
  logger.write( Logger.Level.VERBOSE, "XCFA built, result: " + xcfa.toDot() + "\n")
  return xcfa
}