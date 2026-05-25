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

package hu.bme.mit.theta.xcfa.cli.witnesstransformation

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.c2xcfa.getBoolExpressionFromC
import hu.bme.mit.theta.c2xcfa.getExpressionFromC
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.Logger.Level.INFO
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.cli.params.CFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.ExplPrecSerializer
import hu.bme.mit.theta.xcfa.cli.utils.PredPrecSerializer
import hu.bme.mit.theta.xcfa.toC
import hu.bme.mit.theta.xcfa.witnesses.*
import java.util.*
import kotlin.jvm.optionals.getOrDefault
import kotlin.jvm.optionals.getOrNull
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.encodeToString

class WitnessPredPrecSerializer : PredPrecSerializer {
  override fun serialize(
    prec: Prec,
    config: XcfaConfig<*, *>,
    parseContext: ParseContext,
    logger: Logger,
  ): String {
    val precVars = prec.usedVars
    val scopedVars = precVars.groupByScope(parseContext)
    val scopedPreds =
      (prec as PredPrec)
        .preds
        .filter { ExprUtils.getVars(it).none { it.isInternal(parseContext) } }
        .groupBy { pred ->
          val usedVars = ExprUtils.getVars(pred)
          scopedVars.entries.fold(PrecisionScope(PrecisionScopeType.GLOBAL)) {
            tightest,
            (scope, vars) ->
            if (usedVars.any { vars.contains(it) } && scope.type > tightest.type) scope
            else tightest
          }
        }

    val contents =
      scopedPreds.map { (scope, preds) ->
        val values =
          preds.mapNotNull {
            try {
              val cExpr = it.toC(parseContext)
              precVars.fold(cExpr) { pred, v ->
                pred.replace(v.name.toC(), v.name.split("::").last())
              }
            } catch (e: NotImplementedError) {
              logger.writeln(
                INFO,
                "WARNING: Couldn't serialize precision predicate, skipping it (${e.message})",
              )
              null
            }
          }

        ContentItem(
          precision = Precision(Format.C_EXPRESSION, scope, PrecisionType.PREDICATE, values)
        )
      }

    val witness =
      YamlWitness(
        entryType = EntryType.PRECISION,
        metadata = getMetadata(config),
        content = contents,
      )

    return WitnessYamlConfig.encodeToString(listOf(witness))
  }

  override fun parse(
    input: String,
    currentVars: Iterable<VarDecl<*>>,
    parseContext: ParseContext,
    logger: Logger,
  ): PredPrec {
    if ("" == input) return PredPrec.of()

    val witness =
      WitnessYamlConfig.decodeFromString(ListSerializer(YamlWitness.serializer()), input)[0]
    val predSet =
      witness.content
        .mapNotNull { it.precision }
        .filter { it.type == PrecisionType.PREDICATE }
        .flatMap {
          val vars = currentVars.filterInScope(it.scope, parseContext)
          it.values.mapNotNull { value ->
            try {
              val expr = getBoolExpressionFromC(value, parseContext, false, false, logger, vars)
              ExprUtils.simplify(expr)
            } catch (e: RuntimeException) {
              logger.writeln(
                INFO,
                "WARNING: Couldn't parse initial precision $value, skipping it (${e.message})",
              )
              null
            }
          }
        }

    return PredPrec.of(predSet)
  }
}

class WitnessExplPrecSerializer : ExplPrecSerializer {
  override fun serialize(
    prec: Prec,
    config: XcfaConfig<*, *>,
    parseContext: ParseContext,
    logger: Logger,
  ): String {
    val procedureVars =
      (prec as ExplPrec).vars.filterNot { it.isInternal(parseContext) }.groupByScope(parseContext)

    val contents =
      procedureVars.map { (scope, vars) ->
        val values =
          vars.map {
            val prefix = if (CComplexType.getType(it.ref, parseContext) is CPointer) "" else "&"
            prefix + it.name.split("::").last()
          }
        ContentItem(
          precision = Precision(Format.C_EXPRESSION, scope, PrecisionType.EXPLICIT, values)
        )
      }

    val witness =
      YamlWitness(
        entryType = EntryType.PRECISION,
        metadata = getMetadata(config),
        content = contents,
      )

    return WitnessYamlConfig.encodeToString(listOf(witness))
  }

  override fun parse(
    input: String,
    currentVars: Iterable<VarDecl<*>>,
    parseContext: ParseContext,
    logger: Logger,
  ): ExplPrec {
    if ("" == input) return ExplPrec.empty()

    val witness =
      WitnessYamlConfig.decodeFromString(ListSerializer(YamlWitness.serializer()), input)[0]
    val vars =
      witness.content
        .mapNotNull { it.precision }
        .filter { it.type == PrecisionType.EXPLICIT }
        .flatMap {
          val vars = currentVars.filterInScope(it.scope, parseContext)
          it.values.flatMap { value ->
            try {
              val expr = getExpressionFromC(value, parseContext, false, false, logger, vars)
              ExprUtils.getVars(expr)
            } catch (e: RuntimeException) {
              logger.writeln(
                INFO,
                "WARNING: Couldn't parse initial precision $value, skipping it (${e.message})",
              )
              emptySet()
            }
          }
        }

    return ExplPrec.of(vars)
  }
}

private fun Collection<VarDecl<*>>.groupByScope(parseContext: ParseContext) =
  this.groupBy {
    val scopes = it.name.split("::")
    when (scopes.size) {
      1 -> PrecisionScope(PrecisionScopeType.GLOBAL)
      2 -> PrecisionScope(PrecisionScopeType.FUNCTION, functionName = scopes.first())
      else -> {
        val functionName = scopes.first()
        val line =
          parseContext.metadata.getMetadataValue(it.name, "locationLine").getOrNull() as? Int
            ?: return@groupBy PrecisionScope(
              PrecisionScopeType.FUNCTION,
              functionName = functionName,
            )
        val column =
          parseContext.metadata.getMetadataValue(it.name, "locationColumn").getOrNull() as? Int
        PrecisionScope(
          PrecisionScopeType.LOCATION,
          location = Location(line = line, column = column, function = functionName),
        )
      }
    }
  }

fun VarDecl<*>.isInternal(parseContext: ParseContext): Boolean =
  parseContext.metadata.getMetadataValue(this.name, "cName").isEmpty

private fun getMetadata(config: XcfaConfig<*, *>): Metadata {
  val inputFile = config.inputConfig.input
  return Metadata(
    formatVersion = "2.2",
    uuid = UUID.randomUUID().toString(),
    creationTime = getIsoDate(),
    producer =
      Producer(
        name = (System.getenv("VERIFIER_NAME") ?: "").ifEmpty { "Theta" },
        version = (System.getenv("VERIFIER_VERSION") ?: "").ifEmpty { "no version found" },
      ),
    task =
      Task(
        inputFiles = listOf(inputFile?.name ?: "unknown"),
        inputFileHashes =
          mapOf(Pair(inputFile?.path ?: "unknown", createTaskHash(inputFile?.path ?: "unknown"))),
        specification = config.inputConfig.property.inputProperty.ltl(Unit),
        dataModel =
          (config.frontendConfig.specConfig as? CFrontendConfig)?.architecture?.let {
            if (it == ArchitectureConfig.ArchitectureType.ILP32) DataModel.ILP32 else DataModel.LP64
          } ?: DataModel.ILP32,
        language = Language.C,
      ),
  )
}

fun Iterable<VarDecl<*>>.filterInScope(
  scope: PrecisionScope,
  parseContext: ParseContext,
): List<VarDecl<*>> {
  val preference: (VarDecl<*>, String) -> Int =
    when (scope.type) {
      PrecisionScopeType.GLOBAL -> { varDecl, simpleName ->
          if (varDecl.name == simpleName) 1 else 0
        }
      PrecisionScopeType.FUNCTION -> { varDecl, _ ->
          if (varDecl.name.contains("${scope.functionName}::")) 1 else 0
        }
      else -> { varDecl, _ ->
          val line =
            parseContext.metadata.getMetadataValue(varDecl.name, "locationLine").getOrNull() as? Int
          val column =
            parseContext.metadata.getMetadataValue(varDecl.name, "locationColumn").getOrNull()
              as? Int
          if (line != null && scope.location?.line == line)
            if (column != null && scope.location?.column == column) 3 else 2
          else if (varDecl.name.contains("${scope.functionName}::")) 1 else 0
        }
    }

  val varsInScope =
    fold(mutableMapOf<String, Pair<VarDecl<*>, Int>>()) { vars, it ->
      val simpleName =
        parseContext.metadata.getMetadataValue(it.name, "cName").getOrDefault(it.name) as String
      val pref = preference(it, simpleName)
      if (!vars.containsKey(simpleName) || pref > vars.getValue(simpleName).second)
        vars[simpleName] = Pair(it, pref)
      vars
    }
  return varsInScope.map { it.value.first }
}
