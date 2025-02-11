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
package hu.bme.mit.theta.xcfa.cli.checkers

import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.params.PortfolioConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.portfolio.*
import hu.bme.mit.theta.xcfa.model.XCFA
import java.io.File
import java.io.FileReader
import java.util.concurrent.TimeUnit
import javax.script.Bindings
import javax.script.ScriptEngine
import javax.script.ScriptEngineManager
import javax.script.SimpleBindings

fun getPortfolioChecker(
  xcfa: XCFA,
  mcm: MCM,
  config: XcfaConfig<*, *>,
  parseContext: ParseContext,
  logger: Logger,
  uniqueLogger: Logger,
): SafetyChecker<
  ARG<XcfaState<PtrState<*>>, XcfaAction>,
  Trace<XcfaState<PtrState<*>>, XcfaAction>,
  XcfaPrec<*>,
> = SafetyChecker { _ ->
  val sw = Stopwatch.createStarted()
  val portfolioName = (config.backendConfig.specConfig as PortfolioConfig).portfolio

  val portfolioStm =
    when (portfolioName) {
      "STABLE",
      "CEGAR",
      "COMPLEX",
      "COMPLEX25" -> complexPortfolio25(xcfa, mcm, parseContext, config, logger, uniqueLogger)

      "COMPLEX24" -> complexPortfolio24(xcfa, mcm, parseContext, config, logger, uniqueLogger)

      "COMPLEX23" -> complexPortfolio23(xcfa, mcm, parseContext, config, logger, uniqueLogger)

      "EMERGENT",
      "BOUNDED",
      "BOUNDED25" -> boundedPortfolio25(xcfa, mcm, parseContext, config, logger, uniqueLogger)

      "BOUNDED24" -> boundedPortfolio24(xcfa, mcm, parseContext, config, logger, uniqueLogger)

      "TESTING",
      "CHC",
      "HORN",
      "HORN25" -> hornPortfolio25(xcfa, mcm, parseContext, config, logger, uniqueLogger)

      else -> {
        if (File(portfolioName).exists()) {
          val kotlinEngine: ScriptEngine = ScriptEngineManager().getEngineByExtension("kts")
          val bindings: Bindings = SimpleBindings()
          bindings["xcfa"] = xcfa
          bindings["mcm"] = mcm
          bindings["parseContext"] = parseContext
          bindings["portfolioConfig"] = config
          bindings["logger"] = logger
          bindings["uniqueLogger"] = uniqueLogger
          kotlinEngine.eval(FileReader(portfolioName), bindings) as STM
        } else {
          error("No such file or built-in config: $portfolioName")
        }
      }
    }

  val result = portfolioStm.execute() as Pair<XcfaConfig<*, *>, SafetyResult<*, *>>

  logger.write(
    Logger.Level.RESULT,
    "Config ${result.first} succeeded in ${sw.elapsed(TimeUnit.MILLISECONDS)} ms\n",
  )
  result.second
    as
    SafetyResult<
      ARG<XcfaState<PtrState<*>>, XcfaAction>,
      Trace<XcfaState<PtrState<*>>, XcfaAction>,
    >?
}
