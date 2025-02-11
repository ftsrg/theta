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
package hu.bme.mit.theta.xcfa.cli.witnesses

import hu.bme.mit.theta.analysis.Trace
import java.io.File
import java.io.StringReader
import java.io.StringWriter
import javax.xml.XMLConstants
import javax.xml.transform.OutputKeys
import javax.xml.transform.Source
import javax.xml.transform.Transformer
import javax.xml.transform.TransformerFactory
import javax.xml.transform.stream.StreamResult
import javax.xml.transform.stream.StreamSource

class GraphmlWitness(private val trace: Trace<WitnessNode, WitnessEdge>, programFile: File) {

  private val attributes: MutableList<GraphmlWitnessAttribute> = ArrayList()
  private val data: MutableList<Pair<String, String>> = ArrayList()

  init {
    attributes.add(GraphmlWitnessAttribute("sourcecodelang", "string", "graph", "sourcecodelang"))
    attributes.add(GraphmlWitnessAttribute("creationtime", "string", "graph", "creationtime"))
    attributes.add(GraphmlWitnessAttribute("witness-type", "string", "graph", "witness-type"))
    attributes.add(GraphmlWitnessAttribute("producer", "string", "graph", "producer"))
    attributes.add(GraphmlWitnessAttribute("architecture", "string", "graph", "architecture"))
    attributes.add(GraphmlWitnessAttribute("programHash", "string", "graph", "programhash"))
    attributes.add(GraphmlWitnessAttribute("programfile", "string", "graph", "programfile"))
    attributes.add(GraphmlWitnessAttribute("specification", "string", "graph", "specification"))

    attributes.add(GraphmlWitnessAttribute("assumption", "string", "edge", "assumption"))
    attributes.add(
      GraphmlWitnessAttribute("assumption.scope", "string", "edge", "assumption.scope")
    )
    attributes.add(
      GraphmlWitnessAttribute(
        "assumption.resultfunction",
        "string",
        "edge",
        "assumption.resultfunction",
      )
    )
    attributes.add(GraphmlWitnessAttribute("control", "string", "edge", "control"))
    attributes.add(GraphmlWitnessAttribute("startline", "string", "edge", "startline"))
    attributes.add(GraphmlWitnessAttribute("endline", "string", "edge", "endline"))
    attributes.add(GraphmlWitnessAttribute("startoffset", "string", "edge", "startoffset"))
    attributes.add(GraphmlWitnessAttribute("endoffset", "string", "edge", "endoffset"))
    attributes.add(GraphmlWitnessAttribute("enterLoopHead", "string", "edge", "enterLoopHead"))
    attributes.add(GraphmlWitnessAttribute("enterFunction", "string", "edge", "enterFunction"))
    attributes.add(
      GraphmlWitnessAttribute("returnFromFunction", "string", "edge", "returnFromFunction")
    )
    attributes.add(GraphmlWitnessAttribute("threadId", "string", "edge", "threadId"))
    attributes.add(GraphmlWitnessAttribute("createThread", "string", "edge", "createThread"))
    attributes.add(GraphmlWitnessAttribute("stmt", "string", "edge", "stmt"))
    attributes.add(GraphmlWitnessAttribute("cSource", "string", "edge", "cSource"))

    attributes.add(GraphmlWitnessAttribute("entry", "string", "node", "entry", "false"))
    attributes.add(GraphmlWitnessAttribute("sink", "string", "node", "sink", "false"))
    attributes.add(GraphmlWitnessAttribute("violation", "string", "node", "violation", "false"))
    attributes.add(GraphmlWitnessAttribute("locationStacks", "string", "node", "locationStacks"))
    attributes.add(GraphmlWitnessAttribute("sourceLines", "string", "node", "sourceLines"))
    attributes.add(GraphmlWitnessAttribute("state", "string", "node", "state"))

    data.add(Pair("witness-type", "violation_witness"))
    data.add(Pair("producer", "theta"))
    data.add(Pair("sourcecodelang", "C"))
    data.add(Pair("specification", "CHECK( init(main()), LTL(G ! call(reach_error())) )"))
    data.add(Pair("programfile", programFile.absolutePath))
    data.add(Pair("programhash", createTaskHash(programFile.path)))
    data.add(Pair("architecture", "32bit"))
    data.add(Pair("creationtime", getIsoDate()))
  }

  fun toPrettyXml(): String = prettyFormat(toXml(), 4)

  fun toXml(): String =
    """
<?xml version="1.0" encoding="UTF-8"?>
<graphml xmlns="http://graphml.graphdrawing.org/xmlns" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">

${attributes.map(GraphmlWitnessAttribute::toXml).reduce { a, b -> "$a\n$b" }}
        
<graph edgedefault="directed">

${data.map { "<data key=\"${it.first}\">${it.second}</data>" }.reduce { a, b -> "$a\n$b" }}

${trace.states.map(WitnessNode::toXml).reduce { a, b -> "$a\n$b" }}   
     
${trace.actions.map(WitnessEdge::toXml).reduce { a, b -> "$a\n$b" }}        

</graph>
</graphml>
    """
      .trimIndent()
}

data class GraphmlWitnessAttribute(
  val name: String,
  val type: String,
  val `for`: String,
  val id: String,
  val defaultValue: String? = null,
) {

  fun toXml(): String =
    """
<key attr.name="${escapeXml(name)}" attr.type="${escapeXml(type)}" for="${
        escapeXml(`for`)
    }" id="${escapeXml(id)}" ${
        if (defaultValue == null) "/>" else """
>
<default>$defaultValue</default>
</key>
""".trimIndent()
    }
"""
      .trimIndent()
}

private fun escapeXml(toEscape: String): String {
  var toEscape = toEscape
  toEscape = toEscape.replace("&", "&amp;")
  toEscape = toEscape.replace("\"", "&quot;")
  toEscape = toEscape.replace("'", "&apos;")
  toEscape = toEscape.replace("<", "&lt;")
  toEscape = toEscape.replace(">", "&gt;")
  return toEscape
}

// from https://stackoverflow.com/a/1264912
private fun prettyFormat(input: String, indent: Int): String {
  return try {
    val xmlInput: Source = StreamSource(StringReader(input.replace(Regex("(  )|[\\t\\n\\r]"), "")))
    val stringWriter = StringWriter()
    val xmlOutput = StreamResult(stringWriter)
    val transformerFactory: TransformerFactory = TransformerFactory.newInstance()
    transformerFactory.setAttribute("indent-number", indent)
    transformerFactory.setAttribute(XMLConstants.ACCESS_EXTERNAL_DTD, "")
    transformerFactory.setAttribute(XMLConstants.ACCESS_EXTERNAL_STYLESHEET, "")
    val transformer: Transformer = transformerFactory.newTransformer()
    transformer.setOutputProperty(OutputKeys.INDENT, "yes")
    transformer.transform(xmlInput, xmlOutput)
    xmlOutput.getWriter().toString()
  } catch (e: Exception) {
    System.err.println(input.replace(Regex("(  )|[\\t\\n\\r]"), ""))
    throw RuntimeException(e)
  }
}

fun WitnessNode.toXml(): String =
  """
<node id="$id">
    ${if (entry) "<data key=\"entry\">true</data>" else ""}
    ${if (sink) "<data key=\"sink\">true</data>" else ""}
    ${if (violation) "<data key=\"violation\">true</data>" else ""}
    
    ${
    if (xcfaLocations.isNotEmpty()) "<data key=\"locationStacks\">${
        escapeXml(xcfaLocations.toString())
    }</data>" else ""
}
    ${
    if (cSources.isNotEmpty()) "<data key=\"sourceLines\">${
        escapeXml(cSources.toString())
    }</data>" else ""
}
    ${
    if (globalState != null) "<data key=\"state\">${
        escapeXml(globalState.toString())
    }</data>" else ""
}
</node>
    """
    .trimIndent()

fun WitnessEdge.toXml(): String =
  """
        <edge source="$sourceId" target="$targetId">
            ${if (assumption != null) "<data key=\"assumption\">$assumption</data>" else ""}
            ${if (assumption_scope != null) "<data key=\"assumption.scope\">$assumption_scope</data>" else ""}
            ${if (assumption_resultfunction != null) "<data key=\"assumption.resultfunction\">$assumption_resultfunction</data>" else ""}
            ${if (control != null) "<data key=\"control\">condition-$control</data>" else ""}
            ${if (startline != null && startline != -1) "<data key=\"startline\">$startline</data>" else ""}
            ${if (endline != null && endline != -1) "<data key=\"endline\">$endline</data>" else ""}
            ${if (startoffset != null && startoffset != -1) "<data key=\"startoffset\">$startoffset</data>" else ""}
            ${if (endoffset != null && endoffset != -1) "<data key=\"endoffset\">$endoffset</data>" else ""}
            ${if (enterLoopHead) "<data key=\"enterLoopHead\">true</data>" else ""}
            ${if (enterFunction != null) "<data key=\"enterFunction\">$enterFunction</data>" else ""}
            ${if (returnFromFunction != null) "<data key=\"returnFromFunction\">$returnFromFunction</data>" else ""}
            ${if (threadId != null) "<data key=\"threadId\">$threadId</data>" else ""}
            ${if (createThread != null) "<data key=\"createThread\">$createThread</data>" else ""}

            ${if (stmt != null) "<data key=\"stmt\">${escapeXml(stmt)}</data>" else ""}
            ${
    if (cSource != null && cSource != "") "<data key=\"cSource\">${
        escapeXml(cSource)
    }</data>" else ""
}

        </edge>
    """
    .trimIndent()
