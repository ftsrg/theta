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
        val procedureVars = prec.usedVars.groupByProcedure()
        val procedurePreds = (prec as PredPrec).preds
            .filter { ExprUtils.getVars(it).none(VarDecl<*>::isInternal) }
            .map { it.toC(parseContext) }
            .groupBy { pred ->
                procedureVars.keys.firstOrNull { proc -> // preds without local vars are grouped to null
                    proc?.let{ pred.contains(it) } ?: false
                }
            }
        val contents = procedurePreds.map { (procedure, preds) ->
            val precision = if (procedure == null) { // preds with global variables only
                Precision(
                    type = PrecisionType.PREDICATE,
                    scope = PrecisionScope(PrecisionScopeType.GLOBAL),
                    format = Format.C_EXPRESSION,
                    values = preds,
                )
            } else {
                val vars = procedureVars[procedure] ?: listOf()
                val values = preds.map {
                    vars.fold(it) { pred, v ->
                        pred.replace(v.toC(), v.split("::").last())
                    }
                }
                Precision(
                    type = PrecisionType.PREDICATE,
                    scope = PrecisionScope(PrecisionScopeType.FUNCTION, functionName = procedure),
                    format = Format.C_EXPRESSION,
                    values = values,
                )
            }
            ContentItem(precision = precision)
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
            .flatMap { it.values.mapNotNull { value ->
                try {
                    getBoolExprFromC(value, parseContext, false, false, logger, currentVars)
                } catch (e: RuntimeException) {
                    logger.writeln(Logger.Level.INFO, "WARNING: Couldn't parse initial precision $value, skipping it (${e.message})")
                    null
                }
            } }

        return PredPrec.of(predSet)
    }
}

class WitnessExplPrecSerializer : PrecSerializer<ExplPrec> {
    override fun serialize(prec: Prec): String {
        val procedureVars = (prec as ExplPrec).vars
            .filterNot { it.isInternal }
            .groupByProcedure()
            .mapValues { (_, vars) ->
                vars.map { "&" + it.split("::").last() }
            }

        val contents = procedureVars.map { (procedure, vars) ->
            ContentItem(precision =
                Precision(
                    type = PrecisionType.EXPLICIT,
                    scope = if (procedure == null) PrecisionScope(PrecisionScopeType.GLOBAL)
                            else PrecisionScope(PrecisionScopeType.FUNCTION, functionName = procedure),
                    format = Format.C_EXPRESSION,
                    values = vars,
                )
            )
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
            .flatMap { it.values.flatMap { value ->
                try {
                    val expr = getExpressionFromC(value, parseContext, false, false, logger, currentVars)
                    ExprUtils.getVars(expr)
                } catch (e: RuntimeException) {
                    logger.writeln(Logger.Level.INFO, "WARNING: Couldn't parse initial precision $value, skipping it (${e.message})")
                    emptySet()
                }
            } }

        return ExplPrec.of(vars)
    }
}

private fun Collection<VarDecl<*>>.groupByProcedure() = this
    .map { it.name }
    .groupBy {
        if (it.contains("::")) it.split("::").first()
        else null
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
