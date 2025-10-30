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
package hu.bme.mit.theta.xsts.cli.optiongroup

import com.github.ajalt.clikt.parameters.groups.OptionGroup
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.enum
import com.github.ajalt.clikt.parameters.types.file
import com.github.ajalt.clikt.parameters.types.inputStream
import com.github.ajalt.clikt.parameters.types.int
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet
import hu.bme.mit.theta.frontend.petrinet.model.PropType
import hu.bme.mit.theta.frontend.petrinet.pnml.XMLPnmlToPetrinet
import hu.bme.mit.theta.frontend.petrinet.xsts.PetriNetToXSTS
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.passes.XstsStmtFlatteningTransformer
import hu.bme.mit.theta.xsts.dsl.XstsDslManager
import java.io.*

class InputOptions :
  OptionGroup(name = "Input options", help = "Options related to model and property input") {
  val model: File by
    option(
        help =
          "Path of the input model (XSTS or Pnml). Extension should be .pnml to be handled as petri-net input"
      )
      .file(mustExist = true, canBeDir = false)
      .required()
  private val property: InputStream? by
    option(help = "Path of the property file. Has priority over --inlineProperty").inputStream()
  private val inlineProperty: String? by
    option(help = "Input property as a string. Ignored if --property is defined")
  private val flattenDepth: Int by
    option(
        help =
          "Depth to which the statements of the XSTS model should be flattened. -1 means fully flattened, 0 means no flattening."
      )
      .int()
      .default(2)
  private val initialmarking: String by
    option(help = "Initial marking of the pnml model").default("")
  val pnProperty: PropType by
    option(help = "Property type for Petri-nets")
      .enum<PropType>()
      .default(PropType.FULL_EXPLORATION)

  fun isPnml() = model.path.endsWith("pnml")

  fun loadXsts(): XSTS {
    val propertyStream =
      if (property != null) property
      else
        (if (inlineProperty != null) ByteArrayInputStream("prop { $inlineProperty }".toByteArray())
        else null)
    if (isPnml()) {
      val petriNet = XMLPnmlToPetrinet.parse(model.absolutePath, initialmarking)
      return PetriNetToXSTS.createXSTS(petriNet, propertyStream, pnProperty)
    }
    val parsedXsts =
      XstsDslManager.createXsts(
        SequenceInputStream(FileInputStream(model), propertyStream ?: InputStream.nullInputStream())
      )
    return XstsStmtFlatteningTransformer.transform(parsedXsts, flattenDepth)
  }

  fun loadPetriNet(): MutableList<PetriNet> = /*PetriNetParser.loadPnml(model).parsePTNet()*/
    mutableListOf(XMLPnmlToPetrinet.parse(model.absolutePath, initialmarking))
}
