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
package hu.bme.mit.theta.xcfa.witnesses

import com.charleskorn.kaml.Yaml
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

val WitnessYamlConfig =
  Yaml(configuration = Yaml.default.configuration.copy(encodeDefaults = false))

// https://gitlab.com/sosy-lab/benchmarking/sv-witnesses/-/blob/8f5dc4bf00c01bc6d5636d7993e164d181e19204/violation-witness-schema.yml
// https://gitlab.com/sosy-lab/benchmarking/sv-witnesses/-/blob/8f5dc4bf00c01bc6d5636d7993e164d181e19204/correctness-witness-schema.yml

/**
 * For violations: Each entry consists of three key-value pairs, namely the key `entry_type` with
 * value `violation_sequence`, the key metadata, and the key content. For correctness: The
 * `entry_type` defines what content is available in the content field. The only allowed entry type
 * for a correctness witness is `invariant_set`.
 *
 * @param entryType The `entry_type` defines what content is available in the content field. The
 *   only allowed entry type for a correctness witness is `violation_sequence`.
 * @param metadata The meta data describe the provenance of the data.
 * @param content For violations: The content represents the semantical content of the violation
 *   witness. It is a sequence of one or more segments. The content contains a sequence of zero or
 *   more normal segments and exactly one final segment at the end. For correctness: The content
 *   represents the semantical content of the correctness witness. It is a sequence of one or more
 *   invariant elements.
 */
@Serializable
data class YamlWitness(
  @SerialName("entry_type") val entryType: EntryType,
  val metadata: Metadata,
  val content: List<ContentItem>,
)

@Serializable
enum class EntryType {
  @SerialName("violation_sequence") VIOLATION,
  @SerialName("invariant_set") INVARIANTS,
}

/**
 * The meta data describe the provenance of the data.
 *
 * @param formatVersion The `version` of the format is given as a string (currently "2.0").
 * @param uuid The `uuid` is a unique identifier of the entry; it uses the UUID format defined in
 *   RFC4122.
 * @param creationTime The `creation_time` describes the date and time when the entry was created;
 *   it uses the format given by ISO 8601.
 * @param producer The key `producer` describes the tool that produced the entry.
 */
@Serializable
data class Metadata(
  @SerialName("format_version") val formatVersion: String,
  val uuid: String,
  @SerialName("creation_time") val creationTime: String,
  val producer: Producer,
  val task: Task,
)

/**
 * The key `producer` describes the tool that produced the entry.
 *
 * @param name The name of the tool that produced the witness.
 * @param version The version of the tool
 * @param configuration The configuration in which the tool ran (optional)
 * @param commandLine The command line with which the tool ran; it should be a bash-compliant
 *   command (optional)
 * @param description Any information not fitting in the previous items (optional)
 */
@Serializable
data class Producer(
  val name: String,
  val version: String,
  val configuration: String? = null,
  @SerialName("command_line") val commandLine: String? = null,
  val description: String? = null,
)

/**
 * The task describes the verification task to which the entry is related.
 *
 * @param inputFiles The list of files given as input to the verifier, e.g.
 *   ["path/f1.c", "path/f2.c"].
 * @param inputFileHashes The SHA-256 hashes of all files in input_files, e.g. {"path/f1.c": 511...,
 *   "path/f2.c": f70...}
 * @param specification The specification considered by the verifier; it uses the SV-COMP format
 *   given at https://sv-comp.sosy-lab.org/2023/rules.php.
 * @param dataModel The data model assumed for the input program. (ILP32 / LP64)
 * @param language The programming language of the input files; the format currently supports only
 *   C.
 */
@Serializable
data class Task(
  @SerialName("input_files") val inputFiles: List<String>,
  @SerialName("input_file_hashes") val inputFileHashes: Map<String, String>,
  val specification: String,
  @SerialName("data_model") val dataModel: DataModel,
  val language: Language,
)

@Serializable
enum class DataModel {
  ILP32,
  LP64,
}

@Serializable
enum class Language {
  C
}

/**
 * @param segment A `segment` is a sequence of one or more waypoints. They are used to structure the
 *   waypoints into segments. Each `segment` is a sequence of zero or more waypoints with action
 *   `avoid` and exactly one waypoint of action `follow` at the end. A segment is called _final_ if
 *   it ends with the `target` waypoint and it is called _normal_ otherwise. items: type: object
 *   required: - waypoint properties: waypoint: type: object required: - type - action - location
 *   description: | The `waypoint` elements are the basic building block of violation witnesses.
 *   They have the form of simple restrictions on program executions. Technically, a waypoint is a
 *   mapping with four keys, namely type, location, constraint, and action. The values of the first
 *   three keys specify the requirement on a program execution to pass a waypoint: `type` describes
 *   the type of the requirement, `location` specifies the program location where the requirement is
 *   evaluated, and `constraint` gives the requirement itself and is not allowed for waypoints of
 *   type `function_enter` and `target`. The key `action` then states whether the executions
 *   represented by the witness should pass through the waypoint (value `follow`) or avoid it (value
 *   `avoid`). The format currently supports two possible values of type with the following
 *   meanings: - `assumption`: The location has to point to the beginning of a statement or a
 *   declaration inside a compound statement. A requirement of this type says that a given
 *   constraint is satisfied before the pointed statement or declaration inside a compound
 *   statement. The constraint is a mapping with two keys: `format` specifies the language of the
 *   assumption and `value` contains a side-effect-free assumption over variables in the current
 *   scope. The value of `format` is `c_expression` as C expressions are the only assumptions
 *   currently supported. In future, we plan to support also assumptions in ACSL. - `target`: This
 *   type of requirement can be used only with action `follow` and it marks the program location
 *   where the property is violated. More precisely, the location points at the first character of
 *   the statement or full expression whose evaluation is sequenced directly before the violation
 *   occurs, i.e., there is no other evaluation sequenced before the violation and the sequence
 *   point associated with the location. This also implies that it can only point to a function call
 *   if it calls a function of the C standard library
 * @param invariant The key `invariant` is the basic building block of correctness witnesses. It is
 *   a mapping that describes one invariant.
 */
@Serializable
data class ContentItem(val segment: Segment? = null, val invariant: Invariant? = null) {

  constructor(wpContent: WaypointContent) : this(listOf(Waypoint(wpContent)))
}

typealias Segment = List<Waypoint>

@Serializable data class Waypoint(val waypoint: WaypointContent)

/**
 * The `waypoint` elements are the basic building block of violation witnesses. They have the form
 * of simple restrictions on program executions. Technically, a waypoint is a mapping with four
 * keys, namely type, location, constraint, and action. The values of the first three keys specify
 * the requirement on a program execution to pass a waypoint: `type` describes the type of the
 * requirement, `location` specifies the program location where the requirement is evaluated, and
 * `constraint` gives the requirement itself and is not allowed for waypoints of type
 * `function_enter` and `target`. The key `action` then states whether the executions represented by
 * the witness should pass through the waypoint (value `follow`) or avoid it (value `avoid`). The
 * format currently supports two possible values of type with the following meanings:
 * - `assumption`: The location has to point to the beginning of a statement or a declaration inside
 *   a compound statement. A requirement of this type says that a given constraint is satisfied
 *   before the pointed statement or declaration inside a compound statement. The constraint is a
 *   mapping with two keys: `format` specifies the language of the assumption and `value` contains a
 *   side-effect-free assumption over variables in the current scope. The value of `format` is
 *   `c_expression` as C expressions are the only assumptions currently supported. In future, we
 *   plan to support also assumptions in ACSL.
 * - `target`: This type of requirement can be used only with action `follow` and it marks the
 *   program location where the property is violated. More precisely, the location points at the
 *   first character of the statement or full expression whose evaluation is sequenced directly
 *   before the violation occurs, i.e., there is no other evaluation sequenced before the violation
 *   and the sequence point associated with the location. This also implies that it can only point
 *   to a function call if it calls a function of the C standard library that violates the property
 *   or if the function call itself is the property violation. The key constraint has to be omitted
 *   for type `target`.
 * - `function_enter`: The location points to the right parenthesis after the function arguments at
 *   the call site and the requirement says that the called function is entered. The key constraint
 *   has to be omitted in this case.
 * - `function_return`: Such a requirement says that a given function call has been evaluated and
 *   the returned value satisfies a given constraint. The location points to the right parenthesis
 *   after the function arguments at the call site. The constraint is a mapping with keys format and
 *   value. We currently support only ACSL expressions of the form `\result <op>
 *   <const_expression>`, where `<op>` is one of `==`, `!=`, `<=`, `<`, `>`, `>=` and
 *   `<const_expression>` is a constant expression. The value of format has to be `acsl_expression`.
 * - `branching`: A requirement of this type says that a given branching is evaluated in a given
 *   way. The location points to a branching keyword like `if`, `while`, `switch`, or to the
 *   character `?` in the ternary operator (`?:`). The constraint is then a mapping with only one
 *   key value. For binary branchings, value can be either `true` or `false` saying whether the true
 *   branch is used or not. For the keyword switch, value holds an integer constant or default. The
 *   integer constant specifies the value of the controlling expression of the switch statement. The
 *   value default says that the value of this expression does not match any case of the switch with
 *   the potential exception of the default case.
 *
 * An `assumption` waypoint is evaluated at the sequence point immediately before the waypoint
 * location. The waypoint is passed if the given constraint evaluates to true. A `branching`
 * waypoint is evaluated at the sequence point immediately after evaluation of the controlling
 * expression of the corresponding branching statement. The waypoint is passed if the resulting
 * value of the controlling expression corresponds to the given constraint. A `function_enter`
 * waypoint is evaluated at the sequence point immediately after evaluation of all arguments of the
 * function call. The waypoint is passed without any additional constraint. A `function_return`
 * waypoint is evaluated immediately after evaluation of the corresponding function call. The
 * waypoint is passed if the returned value satisfies the given constraint.
 *
 * @param type
 * @param constraint The constraint of the waypoint. A constraint is not allowed for type `target`.
 * @param location The `location` is a mapping with mandatory keys file_name and line. All other
 *   keys are optional. If the location provides an inconsistent information (e.g., identifier
 *   specifies a function that is not called at the given column on the given line ), the witness is
 *   syntactically invalid.
 * @param action Action `follow` means that the waypoint should be passed through. Action `avoid`
 *   means that the waypoint should be avoided.
 */
@Serializable
data class WaypointContent(
  val type: WaypointType,
  val constraint: Constraint? = null,
  val location: Location,
  val action: Action,
)

@Serializable
enum class WaypointType {
  @SerialName("assumption") ASSUMPTION,
  @SerialName("target") TARGET,
  @SerialName("function_enter") FUNCTION_ENTER,
  @SerialName("function_return") FUNCTION_RETURN,
  @SerialName("branching") BRANCHING,
  @SerialName("recurrence_condition") RECURRENCE_CONDITION,
}

/**
 * The constraint of the waypoint. A constraint is not allowed for type `target`.
 *
 * @param value
 * @param format
 */
@Serializable data class Constraint(val value: String, val format: Format? = null)

@Serializable
enum class Format {
  @SerialName("c_expression") C_EXPRESSION,
  @SerialName("acsl_expression") ACSL_EXPRESSION,
}

/**
 * The `location` is a mapping with mandatory keys file_name and line. All other keys are optional.
 * If the location provides an inconsistent information (e.g., identifier specifies a function that
 * is not called at the given column on the given line ), the witness is syntactically invalid.
 *
 * @param fileName The name of the file of the location
 * @param line The line number pf the program location in the file.
 * @param column The key `column` specifies the column number of the location, i.e., the position of
 *   the `column`-th character in the line that the location points to (value 1 is the position of
 *   the first character). If the column is not given, then it is interpreted as the leftmost
 *   suitable position on the line, where suitability is given by `type`.
 * @param function The key `function` gives the name of the function containing the location. It is
 *   usually determined by the `file_name` and `line`, but the information can improve human
 *   readability of the witness.
 */
@Serializable
data class Location(
  @SerialName("file_name") val fileName: String,
  val line: Int,
  val column: Int? = null,
  val function: String? = null,
)

/**
 * Action `follow` means that the waypoint should be passed through. Action `avoid` means that the
 * waypoint should be avoided.
 */
@Serializable
enum class Action {
  @SerialName("follow") FOLLOW,
  @SerialName("avoid") AVOID,
  @SerialName("cycle") CYCLE,
}

@Serializable
data class Invariant(
  val type: InvariantType,
  val location: Location,
  val value: String,
  val format: Format,
)

@Serializable
enum class InvariantType {
  @SerialName("loop_invariant") LOOP_INVARIANT,
  @SerialName("location_invariant") LOCATION_INVARIANT,
}
