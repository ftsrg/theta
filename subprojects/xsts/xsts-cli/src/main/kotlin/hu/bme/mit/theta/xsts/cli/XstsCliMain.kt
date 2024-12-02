/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xsts.cli

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.subcommands
import com.github.ajalt.clikt.parameters.options.deprecated
import com.github.ajalt.clikt.parameters.options.option

class XstsCliMainCommand : CliktCommand() {

  val algorithm by
    option(eager = true)
      .deprecated(
        "--algorithm switch is now deprecated, use the respective subcommands",
        error = true,
      )
  val metrics by
    option(eager = true)
      .deprecated("--metrics switch is now deprecated, use the `metrics` subcommand", error = true)
  val header by
    option(eager = true)
      .deprecated("--header switch is now deprecated, use the `header` subcommand", error = true)

  override fun run() = Unit
}

fun main(args: Array<String>) =
  XstsCliMainCommand()
    .subcommands(
      XstsCliCegar(),
      XstsCliBounded(),
      XstsCliMdd(),
      XstsCliPetrinetMdd(),
      XstsCliChc(),
      XstsCliHeader(),
      XstsCliMetrics(),
      XstsCliTracegen(),
    )
    .main(args)
