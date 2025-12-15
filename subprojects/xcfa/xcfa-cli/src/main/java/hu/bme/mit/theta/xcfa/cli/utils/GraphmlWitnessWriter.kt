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

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.c2xcfa.getCMetaData
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.XcfaTraceConcretizer
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.targetToWitness
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.traceToWitness
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.witnesses.GraphmlWitness
import hu.bme.mit.theta.xcfa.witnesses.createTaskHash
import java.io.BufferedWriter
import java.io.File
import java.io.FileWriter
import java.io.IOException
import java.text.DateFormat
import java.text.SimpleDateFormat
import java.util.*

class GraphmlWitnessWriter : XcfaWitnessWriter {

  override val extension: String = "graphml"

  override fun writeTrivialCorrectnessWitness(
    safetyResult: SafetyResult<*, *>,
    inputFile: File,
    property: XcfaProperty,
    parseContext: ParseContext,
    witnessfile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType?,
  ) {

    val taskHash = createTaskHash(inputFile.absolutePath)
    val ltlSpecification = property.inputProperty.name
    val dummyWitness = StringBuilder()
    dummyWitness
      .append(
        "<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">"
      )
      .append(System.lineSeparator())
      .append("<key id=\"sourcecodelang\" attr.name=\"sourcecodelang\" for=\"graph\"/>")
      .append(System.lineSeparator())
      .append("<key id=\"witness-type\" attr.name=\"witness-type\" for=\"graph\"/>")
      .append(System.lineSeparator())
      .append("<key id=\"entry\" attr.name=\"entry\" for=\"node\">")
      .append(System.lineSeparator())
      .append("<default>false</default>")
      .append(System.lineSeparator())
      .append("</key>")
      .append(System.lineSeparator())
      .append("<key id=\"invariant\" attr.name=\"invariant\" for=\"node\">")
      .append(System.lineSeparator())
      .append("<default>false</default>")
      .append(System.lineSeparator())
      .append("</key>")
      .append(System.lineSeparator())
      .append(
        "<key attr.name=\"specification\" attr.type=\"string\" for=\"graph\" id=\"specification\"/>"
      )
      .append(System.lineSeparator())
      .append("<key attr.name=\"producer\" attr.type=\"string\" for=\"graph\" id=\"producer\"/>")
      .append(System.lineSeparator())
      .append(
        "<key attr.name=\"programFile\" attr.type=\"string\" for=\"graph\" id=\"programfile\"/>"
      )
      .append(System.lineSeparator())
      .append(
        "<key attr.name=\"programHash\" attr.type=\"string\" for=\"graph\" id=\"programhash\"/>"
      )
      .append(System.lineSeparator())
      .append(
        "<key attr.name=\"architecture\" attr.type=\"string\" for=\"graph\" id=\"architecture\"/>"
      )
      .append(System.lineSeparator())
      .append(
        "<key attr.name=\"creationtime\" attr.type=\"string\" for=\"graph\" id=\"creationtime\"/>"
      )
      .append(System.lineSeparator())
      .append("<graph edgedefault=\"directed\">")
      .append(System.lineSeparator())
      .append("<data key=\"witness-type\">correctness_witness</data>")
      .append(System.lineSeparator())
      .append("<data key=\"producer\">theta</data>")
      .append(System.lineSeparator())
      .append("<data key=\"specification\">$ltlSpecification</data>")
      .append(System.lineSeparator())
      .append("<data key=\"sourcecodelang\">C</data>")
      .append(System.lineSeparator())
      .append("<data key=\"architecture\">32bit</data>")
      .append(System.lineSeparator())
      .append("<data key=\"programhash\">")
    dummyWitness.append(taskHash)
    dummyWitness
      .append("</data>")
      .append(System.lineSeparator())
      .append("<data key=\"creationtime\">")

    val tz: TimeZone = TimeZone.getTimeZone("UTC")
    val df: DateFormat =
      SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss'Z'") // Quoted "Z" to indicate UTC, no timezone offset

    df.timeZone = tz
    val isoDate: String = df.format(Date())

    dummyWitness.append(isoDate)
    dummyWitness
      .append("</data>")
      .append(System.lineSeparator())
      .append("<data key=\"programfile\">")
    dummyWitness.append(inputFile.name)
    dummyWitness
      .append("</data>")
      .append(System.lineSeparator())
      .append("<node id=\"N0\">")
      .append(System.lineSeparator())
      .append("<data key=\"entry\">true</data>")
      .append(System.lineSeparator())
      .append("</node>")
      .append(System.lineSeparator())
      .append("</graph>")
      .append(System.lineSeparator())
      .append("</graphml>")

    try {
      BufferedWriter(FileWriter(witnessfile)).use { bw -> bw.write(dummyWitness.toString()) }
    } catch (ioe: IOException) {
      ioe.printStackTrace()
    }
  }

  fun generateTrivialViolationWitness(
    safetyResult: SafetyResult<*, *>,
    inputFile: File,
    property: XcfaProperty,
    parseContext: ParseContext,
    witnessfile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType?,
    startline: Int,
    endline: Int,
    startoffset: Int,
    endoffset: Int,
  ): String {
    val witnessTrace = targetToWitness(startline, endline, startoffset, endoffset)
    val emptyWitness = GraphmlWitness(null, inputFile, ltlSpecification)
    val xml = emptyWitness.toPrettyXml()
    return injectContent(xml, witnessTrace)
  }

  private fun injectContent(xml: String, content: String): String {
    val closingGraph = "</graph>"
    val index = xml.indexOf(closingGraph)
    require(index != -1) { "No </graph> tag found in XML" }
    val builder = StringBuilder()
    builder.append(xml.substring(0, index)) // everything before </graph>
    builder.append(content) // insert your content inside <graph>
    builder.append(closingGraph) // re-add </graph>
    builder.append(xml.substring(index + closingGraph.length)) // rest of file (</graphml> etc.)
    return builder.toString()
  }

  override fun generateEmptyViolationWitness(
    inputFile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType?,
  ): String {
    val emptyWitnessContent =
      """
      <node id="N0">
      <data key="violation">true</data>
      <data key="entry">true</data>
      </node>
  """
        .trimIndent()
    val emptyWitness = GraphmlWitness(null, inputFile, ltlSpecification)
    val xml = emptyWitness.toPrettyXml()
    return injectContent(xml, emptyWitnessContent)
  }

  override fun writeWitness(
    safetyResult: SafetyResult<*, *>,
    inputFile: File,
    property: XcfaProperty,
    cexSolverFactory: SolverFactory,
    parseContext: ParseContext,
    witnessfile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType?,
    logger: Logger,
  ) {
    // TODO eliminate the need for the instanceof check
    if (safetyResult.isUnsafe && safetyResult.asUnsafe().cex is Trace<*, *>) {
      try {
        val concrTrace: Trace<XcfaState<ExplState>, XcfaAction> =
          XcfaTraceConcretizer.concretize(
            safetyResult.asUnsafe().cex as Trace<XcfaState<PtrState<*>>, XcfaAction>?,
            cexSolverFactory,
            parseContext,
          )

        val witnessTrace =
          traceToWitness(trace = concrTrace, parseContext = parseContext, property = property)
        val graphmlWitness = GraphmlWitness(witnessTrace, inputFile, ltlSpecification)
        val xml = graphmlWitness.toPrettyXml()
        witnessfile.writeText(xml)
      } catch (e: Exception) {
        logger.info("Could not emit witness, keeping target only: ${e.message}")
        val lastLabel =
          (safetyResult.asUnsafe().cex as Trace<*, XcfaAction>)
            .actions
            .flatMap { it.label.getFlatLabels() }
            .findLast { it -> it.metadata.isSubstantial() }
        val metadata = lastLabel?.getCMetaData()
        val startline: Int? = (metadata as? CMetaData)?.lineNumberStart
        val endline: Int? = (metadata as? CMetaData)?.lineNumberStop
        val startoffset: Int? = (metadata as? CMetaData)?.offsetStart
        val endoffset: Int? = (metadata as? CMetaData)?.offsetEnd
        val witness =
          if (startline != null && endline != null && startoffset != null && endoffset != null) {
            generateTrivialViolationWitness(
              safetyResult = safetyResult,
              inputFile = inputFile,
              property = property,
              parseContext = parseContext,
              witnessfile = witnessfile,
              ltlSpecification = ltlSpecification,
              architecture = architecture,
              startline,
              endline,
              startoffset,
              endoffset,
            )
          } else {
            generateEmptyViolationWitness(inputFile, ltlSpecification, architecture)
          }
        witnessfile.writeText(witness)
      }
    } else if (safetyResult.isSafe) {
      writeTrivialCorrectnessWitness(
        safetyResult = safetyResult,
        inputFile = inputFile,
        architecture = architecture,
        parseContext = parseContext,
        ltlSpecification = ltlSpecification,
        witnessfile = witnessfile,
        property = property,
      )
    }
  }
}
