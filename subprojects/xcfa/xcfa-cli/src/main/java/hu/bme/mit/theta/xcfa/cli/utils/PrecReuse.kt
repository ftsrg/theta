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

import com.google.common.base.Preconditions
import com.google.common.collect.Lists
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.utils.PrecCache
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.Logger.Level.INFO
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.rattype.RatExprs
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibDeclTransformer
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel
import hu.bme.mit.theta.solver.smtlib.solver.parser.GeneralResponse
import hu.bme.mit.theta.solver.smtlib.solver.parser.PrecisionResponse
import hu.bme.mit.theta.solver.smtlib.solver.parser.ThrowExceptionErrorListener
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.cli.params.Domain
import hu.bme.mit.theta.xcfa.cli.params.Domain.*
import hu.bme.mit.theta.xcfa.cli.params.InitPrec
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.WitnessExplPrecSerializer
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.WitnessPredPrecSerializer
import hu.bme.mit.theta.xcfa.model.XCFA
import java.io.File
import kotlin.reflect.KProperty
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

enum class PrecReuseFormat(
  val explPrecSerializer: ExplPrecSerializer,
  val predPrecSerializer: PredPrecSerializer,
  val extension: String,
) {
  GENERIC(
    explPrecSerializer = GenericExplPrecSerializer(),
    predPrecSerializer = GenericPredPrecSerializer(),
    extension = "txt",
  ),
  WITNESS(
    explPrecSerializer = WitnessExplPrecSerializer(),
    predPrecSerializer = WitnessPredPrecSerializer(),
    extension = "yml",
  ),
}

enum class PrecSerializationMode {
  NEVER,
  LAST,
  CONTINUOUS,
}

object PrecReuse {
  private const val ERROR_MESSAGE = "Misconfigured WitnessPrecSerializer"

  private var emptyPrec: Prec by ThrowIfNullDelegate("$ERROR_MESSAGE - domain was not set")
  private var prec: Prec? = null
  private var serializer: ((PrecReuseFormat) -> PrecSerializer<*>) by
    ThrowIfNullDelegate("$ERROR_MESSAGE - domain was not set")

  fun setDomain(domain: Domain) {
    serializer =
      when (domain) {
        EXPL -> { format -> format.explPrecSerializer }
        PRED_BOOL,
        PRED_CART,
        PRED_SPLIT -> { format -> format.predPrecSerializer }
        EXPL_PRED_SPLIT,
        EXPL_PRED_STMT -> error("REUSE is not supported for the product domain.")
      }
    emptyPrec = domain.initPrec(XCFA("", emptySet()), InitPrec.EMPTY).unwrap()
  }

  fun load(
    precFilePath: String?,
    currentVars: Iterable<VarDecl<*>> = emptyList(),
    parseContext: ParseContext,
    logger: Logger,
  ) {
    precFilePath
      ?: return warnInitEmptyPrec(
        logger,
        "WARNING: Precision reuse selected, but no precision file specified. Use the --prec-file to provide the precision.",
      )

    val precFile =
      File(precFilePath).takeIf(File::exists)
        ?: return warnInitEmptyPrec(
          logger,
          "WARNING: Precision reuse selected, but provided precision file does not exist.",
        )

    val format =
      PrecReuseFormat.entries.firstOrNull { it.extension == precFile.extension }
        ?: return warnInitEmptyPrec(
          logger,
          "WARNING: Precision reuse selected, but provided precision file format not recognised.",
        )

    prec = serializer(format).parse(precFile.readText(), currentVars, parseContext, logger)
  }

  fun <P : Prec> get(): P =
    prec as? P ?: throw RuntimeException("$ERROR_MESSAGE - incompatible domains")

  fun write(
    outputFolder: File,
    config: XcfaConfig<*, *>,
    parseContext: ParseContext,
    logger: Logger,
  ) {
    config.outputConfig.precOutputConfig.format.forEach { format ->
      val outputFileName = "prec.${format.extension}"
      val outputFile = File(outputFolder, outputFileName)
      outputFile.writeText(
        (PrecCache.get()?.unwrap() ?: emptyPrec).let {
          serializer(format).serialize(it, config, parseContext, logger)
        }
      )
    }
  }

  private fun warnInitEmptyPrec(logger: Logger, message: String) {
    prec = emptyPrec
    logger.writeln(INFO, "$message Proceeding with empty initial precision.")
  }
}

interface PrecSerializer<out P : Prec> {
  fun serialize(
    prec: Prec,
    config: XcfaConfig<*, *>,
    parseContext: ParseContext,
    logger: Logger,
  ): String

  fun parse(
    input: String,
    currentVars: Iterable<VarDecl<*>>,
    parseContext: ParseContext,
    logger: Logger,
  ): P
}

interface ExplPrecSerializer : PrecSerializer<ExplPrec>

interface PredPrecSerializer : PrecSerializer<PredPrec>

class GenericExplPrecSerializer : ExplPrecSerializer {
  override fun serialize(
    prec: Prec,
    config: XcfaConfig<*, *>,
    parseContext: ParseContext,
    logger: Logger,
  ) =
    "*:\n" +
      prec.usedVars
        .joinToString(separator = "\n") { it.name }
        .also {
          logger.writeln(INFO, "FinalPrecisionsUsed: ${prec.usedVars.size}")
          logger.writeln(INFO, "FinalPrecisionsExported: ${prec.usedVars.size}")
        }

  override fun parse(
    input: String,
    currentVars: Iterable<VarDecl<*>>,
    parseContext: ParseContext,
    logger: Logger,
  ): ExplPrec {
    val varNames = removeScopes(input).trim().split(Regex("\\s+"))
    val vars = currentVars.filter { varNames.contains(it.name) }

    logger.writeln(INFO, "InitialPrecisionsFound: ${varNames.size}")
    logger.writeln(INFO, "InitialPrecisionsUsed: ${vars.size}")

    return ExplPrec.of(vars)
  }
}

class GenericPredPrecSerializer : PredPrecSerializer {
  override fun serialize(
    prec: Prec,
    config: XcfaConfig<*, *>,
    parseContext: ParseContext,
    logger: Logger,
  ): String {
    val symbolTable = PrecSmtLibSymbolTable()
    val transformationManager = GenericSmtLibTransformationManager(symbolTable)
    val declTransformer = PrecSmtLibDeclTransformer(transformationManager, symbolTable)

    val quotedVarLookup = prec.usedVars.associateWith { Decls.Const(it.toSymbol(), it.type) }

    val varDecls =
      quotedVarLookup.values.joinToString(separator = "\n") { declTransformer.toDeclaration(it) }

    val predicates =
      (prec as PredPrec)
        .preds
        .map { pred -> ExprUtils.changeDecls(pred, quotedVarLookup) }
        .mapNotNull {
          try {
            transformationManager.toTerm(it)
          } catch (e: Exception) {
            logger.writeln(
              INFO,
              "WARNING: Couldn't serialize precision predicate, skipping it (${e.message})",
            )
            null
          }
        }
    val joinedPreds = predicates.joinToString(separator = "\n") { "(assert $it)" }

    logger.writeln(INFO, "FinalPrecisionsUsed: ${prec.preds.size}")
    logger.writeln(INFO, "FinalPrecisionsExported: ${predicates.size}")

    return (if (varDecls.isNotEmpty()) "$varDecls\n\n" else "") + "*:\n$joinedPreds"
  }

  override fun parse(
    input: String,
    currentVars: Iterable<VarDecl<*>>,
    parseContext: ParseContext,
    logger: Logger,
  ): PredPrec {
    val symbolTable = PrecSmtLibSymbolTable()
    val termTransformer = GenericSmtLibTermTransformer(symbolTable)

    val savedPrec = parseResponse(removeScopes(input))
    val funDecls = savedPrec.funDeclarations

    funDecls.forEach { (name, def) ->
      var type = transformSort(def.get2())
      for (s in Lists.reverse(def.get1())) {
        type = FuncType.of(transformSort(s), type)
      }
      symbolTable.put(Decls.Const(name, type), name, def.get3())
    }

    val varLookup =
      funDecls.keys
        .associateBy(symbolTable::getConst) { name -> currentVars.find { it.toSymbol() == name } }
        .filterValues { it != null }

    val preds =
      savedPrec.terms.mapNotNull { t ->
        try {
          var expr = termTransformer.toExpr(t, BoolExprs.Bool(), SmtLibModel(emptyMap()))
          expr = ExprUtils.changeDecls(expr, varLookup)
          ExprUtils.simplify(expr)
        } catch (e: Exception) {
          logger.writeln(
            INFO,
            "WARNING: Couldn't parse initial precision $t, skipping it (${e.message})",
          )
          null
        }
      }

    logger.writeln(INFO, "InitialPrecisionsFound: ${savedPrec.terms.size}")
    logger.writeln(INFO, "InitialPrecisionsUsed: ${preds.size}")

    return PredPrec.of(preds)
  }
}

fun Prec.unwrap(): Prec =
  when (this) {
    is XcfaPrec<*> -> this.p.unwrap()
    is PtrPrec<*> -> this.innerPrec.unwrap()
    is ExplPrec,
    is PredPrec -> this
    else -> error("Precision serialization is not supported for ${this::class}.")
  }

class PrecSmtLibSymbolTable : GenericSmtLibSymbolTable() {
  override fun put(constDecl: ConstDecl<*>, symbol: String, declaration: String) {
    Preconditions.checkState(!constToSymbol.containsKey(constDecl), "Constant not found.")
    constToSymbol[constDecl] = symbol
    constToDeclaration[constDecl] = declaration
  }

  override fun definesSymbol(symbol: String) = constToSymbol.inverse().containsKey(symbol)
}

class PrecSmtLibDeclTransformer(
  transformer: SmtLibTransformationManager,
  symbolTable: SmtLibSymbolTable,
) : GenericSmtLibDeclTransformer(transformer, symbolTable) {

  override fun symbolNameFor(decl: Decl<*>): String {
    return decl.name
  }
}

private fun Decl<*>.toSymbol() = GenericSmtLibSymbolTable.encodeSymbol(name)

private fun transformSort(ctx: SMTLIBv2Parser.SortContext): Type {
  val name = ctx.identifier().symbol().text
  return when (name) {
    "Int" -> IntExprs.Int()
    "Bool" -> BoolExprs.Bool()
    "Real" -> RatExprs.Rat()
    "BitVec" -> {
      assert(ctx.identifier().index().size == 1)
      BvExprs.BvType(ctx.identifier().index()[0].text.toInt())
    }

    "Array" -> {
      assert(ctx.sort().size == 2)
      ArrayExprs.Array(transformSort(ctx.sort()[0]), transformSort(ctx.sort()[1]))
    }

    else -> throw UnsupportedOperationException()
  }
}

private fun parseResponse(input: String): PrecisionResponse {
  try {
    val lexer = SMTLIBv2Lexer(CharStreams.fromString(input))
    val parser = SMTLIBv2Parser(CommonTokenStream(lexer))
    lexer.removeErrorListeners()
    lexer.addErrorListener(ThrowExceptionErrorListener())
    parser.removeErrorListeners()
    parser.addErrorListener(ThrowExceptionErrorListener())

    val response = GeneralResponse.fromContext(parser.response())
    if (response.isError) {
      throw SmtLibSolverException(response.reason)
    } else if (!(response.isSpecific && response.asSpecific().isPrecisionResponse)) {
      throw RuntimeException("Unable to parse precision")
    }
    return response.asSpecific().asPrecisionResponse()
  } catch (e: Exception) {
    throw SmtLibSolverException("Could not parse solver output: $input", e)
  }
}

fun removeScopes(input: String) =
  input
    .lines()
    .filter { line -> line.trim().let { it.isNotEmpty() && ':' != it.last() } }
    .joinToString("\n")

class ThrowIfNullDelegate<T, P>(private val errorMessage: String) {
  var value: P? = null

  operator fun getValue(thisRef: T?, property: KProperty<*>): P {
    return value ?: throw NullPointerException("$errorMessage: ${property.name} is null")
  }

  operator fun setValue(thisRef: T?, property: KProperty<*>, value: P) {
    this.value = value
  }
}
