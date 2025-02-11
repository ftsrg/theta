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
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.boolean
import com.github.ajalt.clikt.parameters.types.enum
import com.github.ajalt.clikt.parameters.types.file
import hu.bme.mit.theta.common.logging.Logger
import java.io.File

class OutputOptions :
  OptionGroup(name = "Output options", help = "Options related to output and statistics") {

  val logLevel: Logger.Level by
    option(help = "Detailedness of logging").enum<Logger.Level>().default(Logger.Level.SUBSTEP)
  val benchmarkMode: Boolean by
    option("--benchmark", help = "Quiet mode, output will be just the result metrics")
      .boolean()
      .default(false)

  val cexfile: File? by option(help = "Write concrete counterexample to a file").file()
  val stacktrace: Boolean by option(help = "Print stack trace of exceptions").flag()
  val visualize: File? by
    option(help = "Write proof or counterexample to file in dot format").file()
}
