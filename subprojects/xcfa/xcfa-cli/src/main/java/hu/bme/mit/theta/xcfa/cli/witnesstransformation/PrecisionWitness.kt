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

package hu.bme.mit.theta.xcfa.cli.witnesstransformation

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.utils.PrecSerializer
import hu.bme.mit.theta.c2xcfa.getBoolExprFromC
import hu.bme.mit.theta.c2xcfa.getExpressionFromC
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.WitnessPrecSerializerConfig.architecture
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.WitnessPrecSerializerConfig.inputFile
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.WitnessPrecSerializerConfig.logger
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.WitnessPrecSerializerConfig.parseContext
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.WitnessPrecSerializerConfig.property
import hu.bme.mit.theta.xcfa.toC
import hu.bme.mit.theta.xcfa.witnesses.*
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.encodeToString
import java.io.File
import java.util.*
import kotlin.jvm.optionals.getOrDefault
import kotlin.jvm.optionals.getOrNull
import kotlin.reflect.KProperty

object WitnessPrecSerializerConfig {
    private const val ERROR_MESSAGE = "Misconfigured WitnessPrecSerializer"

    var parseContext: ParseContext by ThrowIfNullDelegate(ERROR_MESSAGE)
    var logger: Logger by ThrowIfNullDelegate(ERROR_MESSAGE)
    var inputFile: File? = null
    var property: ErrorDetection? = null
    var architecture: ArchitectureConfig.ArchitectureType? = null
}

class WitnessPredPrecSerializer : PrecSerializer<PredPrec> {
    override fun serialize(prec: Prec): String {
        val precVars = prec.usedVars
        val scopedVars = precVars.groupByScope()
        val scopedPreds = (prec as PredPrec).preds
            .filter { ExprUtils.getVars(it).none(VarDecl<*>::isInternal) }
            .groupBy { pred ->
                val usedVars = ExprUtils.getVars(pred)
                scopedVars.entries.fold(PrecisionScope(PrecisionScopeType.GLOBAL)) { tightest, (scope, vars) ->
                    if (usedVars.any { vars.contains(it) } && scope.type > tightest.type) scope
                    else tightest
                }
            }

        val contents = scopedPreds.map { (scope, preds) ->
            val values = preds.mapNotNull {
                try {
                    val cExpr = it.toC(parseContext)
                    precVars.fold(cExpr) { pred, v ->
                        pred.replace(v.name.toC(), v.name.split("::").last())
                    }
                } catch (e: NotImplementedError) {
                    logger.writeln(Logger.Level.INFO, "WARNING: Couldn't serialize initial precision predicate, skipping it (${e.message})")
                    null
                }
            }

            ContentItem(precision = Precision(Format.C_EXPRESSION, scope, PrecisionType.PREDICATE, values))
        }

        val witness = YamlWitness(
            entryType = EntryType.PRECISION,
            metadata = getMetadata(),
            content = contents
        )

        return WitnessYamlConfig.encodeToString(listOf(witness))
    }

    override fun parse(input: String, currentVars: Iterable<VarDecl<*>>): PredPrec {
        if ("" == input) return PredPrec.of()

        val witness = WitnessYamlConfig.decodeFromString(ListSerializer(YamlWitness.serializer()), input)[0]
        val predSet = witness.content
            .mapNotNull { it.precision }
            .filter { it.type == PrecisionType.PREDICATE }
            .flatMap {
                val vars = currentVars.filterInScope(it.scope)
                it.values.mapNotNull { value ->
                    try {
                        val expr = getBoolExprFromC(value, parseContext, false, false, logger, vars)
                        ExprUtils.simplify(expr)
                    } catch (e: RuntimeException) {
                        logger.writeln(Logger.Level.INFO, "WARNING: Couldn't parse initial precision $value, skipping it (${e.message})")
                        null
                    }
                }
            }

        return PredPrec.of(predSet)
    }
}

class WitnessExplPrecSerializer : PrecSerializer<ExplPrec> {
    override fun serialize(prec: Prec): String {
        val procedureVars = (prec as ExplPrec).vars
            .filterNot { it.isInternal }
            .groupByScope()

        val contents = procedureVars.map { (scope, vars) ->
            val values = vars.map {
                val prefix = if (CComplexType.getType(it.ref, parseContext) is CPointer) "" else "&"
                prefix + it.name.split("::").last()
            }
            ContentItem(precision = Precision(Format.C_EXPRESSION, scope, PrecisionType.EXPLICIT, values))
        }

        val witness = YamlWitness(
            entryType = EntryType.PRECISION,
            metadata = getMetadata(),
            content = contents
        )

        return WitnessYamlConfig.encodeToString(listOf(witness))
    }

    override fun parse(input: String, currentVars: Iterable<VarDecl<*>>): ExplPrec {
        if ("" == input) return ExplPrec.empty()

        val witness = WitnessYamlConfig.decodeFromString(ListSerializer(YamlWitness.serializer()), input)[0]
        val vars = witness.content
            .mapNotNull { it.precision }
            .filter { it.type == PrecisionType.EXPLICIT }
            .flatMap {
                val vars = currentVars.filterInScope(it.scope)
                it.values.flatMap { value ->
                    try {
                        val expr = getExpressionFromC(value, parseContext, false, false, logger, vars)
                        ExprUtils.getVars(expr)
                    } catch (e: RuntimeException) {
                        logger.writeln(Logger.Level.INFO, "WARNING: Couldn't parse initial precision $value, skipping it (${e.message})")
                        emptySet()
                    }
                }
            }

        return ExplPrec.of(vars)
    }
}

private fun Collection<VarDecl<*>>.groupByScope() = this
    .groupBy {
        val scopes = it.name.split("::")
        when (scopes.size) {
            1 -> PrecisionScope(PrecisionScopeType.GLOBAL)
            2 -> PrecisionScope(PrecisionScopeType.FUNCTION, functionName = scopes.first())
            else -> {
                val functionName = scopes.first()
                val line = parseContext.metadata.getMetadataValue(it.name, "locationLine").getOrNull() as? Int
                    ?: return@groupBy PrecisionScope(PrecisionScopeType.FUNCTION, functionName = functionName)
                val column = parseContext.metadata.getMetadataValue(it.name, "locationColumn").getOrNull() as? Int
                PrecisionScope(
                    PrecisionScopeType.LOCATION,
                    location = Location(line = line, column = column, function = functionName)
                )
            }
        }
    }

val VarDecl<*>.isInternal: Boolean
    get() = parseContext.metadata.getMetadataValue(this.name, "cName").isEmpty

private fun getMetadata() =
    Metadata(
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
            inputFileHashes = mapOf(Pair(inputFile?.path ?: "unknown", createTaskHash(inputFile?.path ?: "unknown"))),
            specification = property?.name ?: "unknown",
            dataModel =
            architecture?.let {
                if (it == ArchitectureConfig.ArchitectureType.ILP32) DataModel.ILP32
                else DataModel.LP64
            } ?: DataModel.ILP32,
            language = Language.C,
        ),
    )

class ThrowIfNullDelegate<T, P>(private val errorMessage: String) {
    var value: P? = null

    operator fun getValue(thisRef: T?, property: KProperty<*>): P {
        return value ?: throw NullPointerException("$errorMessage: ${property.name} is null")
    }

    operator fun setValue(thisRef: T?, property: KProperty<*>, value: P) {
        this.value = value
    }
}

fun Iterable<VarDecl<*>>.filterInScope(scope: PrecisionScope): List<VarDecl<*>> {
    val preference: (VarDecl<*>, String) -> Int = when (scope.type) {
        PrecisionScopeType.GLOBAL -> { varDecl, simpleName ->
            if (varDecl.name == simpleName) 1 else 0
        }
        PrecisionScopeType.FUNCTION -> { varDecl, _ ->
            if (varDecl.name.contains("${scope.functionName}::")) 1 else 0
        }
        else -> { varDecl, _ ->
            val line = parseContext.metadata.getMetadataValue(varDecl.name, "locationLine").getOrNull() as? Int
            val column = parseContext.metadata.getMetadataValue(varDecl.name, "locationColumn").getOrNull() as? Int
            if (line != null && scope.location?.line == line)
                if (column != null && scope.location?.column == column) 3 else 2
            else
                if (varDecl.name.contains("${scope.functionName}::")) 1 else 0
        }
    }

    val varsInScope = fold(mutableMapOf<String, Pair<VarDecl<*>, Int>>()) { vars, it ->
        val simpleName = parseContext.metadata.getMetadataValue(it.name, "cName").getOrDefault(it.name) as String
        val pref = preference(it, simpleName)
        if (!vars.containsKey(simpleName) || pref > vars.getValue(simpleName).second)
            vars[simpleName] = Pair(it, pref)
        vars
    }
    return varsInScope.map { it.value.first }
}
