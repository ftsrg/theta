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
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import java.io.File

class PetrinetDependencyOutputOptions : OptionGroup() {

  val depGxl: File? by
    option(
        help = "Generate GXL representation of (extended) dependency graph for variable ordering"
      )
      .file(mustExist = false, canBeDir = false, mustBeWritable = true)
  val depGxlGsat: File? by
    option(
        help = "Generate GXL representation of (extended) dependency graph for variable ordering"
      )
      .file(mustExist = false, canBeDir = false, mustBeWritable = true)
  val depMat: File? by
    option(help = "Generate dependency matrix from the model as a CSV file")
      .file(mustExist = false, canBeDir = false, mustBeWritable = true)
  val depMatPng: File? by
    option(help = "Generate dependency matrix from the model as a PNG file")
      .file(mustExist = false, canBeDir = false, mustBeWritable = true)
}
