package hu.bme.mit.theta.witness.yaml.serialization

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/** Necessary classes to parse yaml, but we will move the parsed data to
* classes into the Witness2 class,
* as yaml parsing handles heterogeneous lists poorly
*/

@Serializable
data class YamlWitnessEntry(
    val entry_type: EntryType,
    val metadata: YamlMetadata,
    val content: List<YamlContent>,
)

@Serializable
enum class EntryType {
    @SerialName("violation_sequence") VIOLATION_SEQUENCE
}

@Serializable
data class YamlMetadata(
    val format_version: String,
    val uuid: String,
    val creation_time: String,
    val producer: YamlProducer,
    val task: YamlTask,
)

@Serializable
data class YamlProducer(
    val name: String,
    val version: String,
    val configuration: String? = null,
    val command_line: String? = null,
    val description: String? = null,
)

@Serializable
data class YamlTask(
    val input_files: List<String>,
    val input_file_hashes: Map<String, String>,
    val specification: String,
    val data_model: String,
    val language: String,
)

@Serializable
data class YamlContent (
    val segment: List<YamlSegment>? = null,
    val cycle: List<YamlCycle>? = null
)

@Serializable
data class YamlSegment(
    val waypoint: YamlWaypoint? = null,
)

@Serializable
data class YamlCycle(
    val segment: List<YamlSegment>? = null,
    val honda: YamlHonda? = null,
)

@Serializable
data class YamlWaypoint(
    val type: WaypointType,
    val constraint: YamlConstraint? = null,
    val location: YamlLocation,
    val action: ActionEnum,
)

@Serializable
enum class WaypointType {
    @SerialName("assumption") ASSUMPTION,
    @SerialName("target") TARGET,
    @SerialName("function_enter") FUNCTION_ENTER,
    @SerialName("function_return") FUNCTION_RETURN,
    @SerialName("branching") BRANCHING,
}

@Serializable()
enum class ActionEnum {
    @SerialName("follow") FOLLOW,
    @SerialName("avoid") AVOID
}

@Serializable
data class YamlConstraint(
    val value: String,
    val format: FormatEnum? = null,
)

@Serializable
enum class FormatEnum {
    @SerialName("c_expression") C_EXPRESSION,
    @SerialName("acsl_expression") ACSL_EXPRESSION
}

@Serializable
data class YamlLocation(
    val file_name: String,
    val line: Int,
    val column: Int? = null,
    val function: String? = null
)

@Serializable
data class YamlHonda(
    val location: YamlLocation,
    val value: String,
    val format: String,
    val invariant: Boolean,
    val inductive: Boolean
)
