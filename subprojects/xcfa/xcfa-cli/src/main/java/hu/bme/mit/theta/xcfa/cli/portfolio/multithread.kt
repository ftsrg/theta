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
package hu.bme.mit.theta.xcfa.cli.portfolio

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.ErrorDetection.DATA_RACE
import hu.bme.mit.theta.xcfa.ErrorDetection.ERROR_LOCATION
import hu.bme.mit.theta.xcfa.analysis.oc.AutoConflictFinderConfig
import hu.bme.mit.theta.xcfa.analysis.oc.OcDecisionProcedureType
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.params.Backend.OC
import hu.bme.mit.theta.xcfa.cli.params.ConeOfInfluenceMode.COI
import hu.bme.mit.theta.xcfa.cli.params.ConeOfInfluenceMode.NO_COI
import hu.bme.mit.theta.xcfa.cli.params.Domain.EXPL
import hu.bme.mit.theta.xcfa.cli.params.Domain.PRED_CART
import hu.bme.mit.theta.xcfa.cli.params.InitPrec.ALLASSUMES
import hu.bme.mit.theta.xcfa.cli.params.POR.AASPOR
import hu.bme.mit.theta.xcfa.cli.params.POR.SPOR
import hu.bme.mit.theta.xcfa.cli.params.Refinement.*
import hu.bme.mit.theta.xcfa.cli.params.Search.*
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.optimizeFurther
import hu.bme.mit.theta.xcfa.passes.*
import hu.bme.mit.theta.xcfa.passes.LbePass.LbeLevel.LBE_LOCAL
import hu.bme.mit.theta.xcfa.passes.LbePass.LbeLevel.NO_LBE

@Suppress("LocalVariableName")
fun multithreadPortfolio(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {

  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  var baseConfig: XcfaConfig<CFrontendConfig, CegarConfig> =
    baseCegarConfig(xcfa, mcm, parseContext, portfolioConfig, false)
      as XcfaConfig<CFrontendConfig, CegarConfig>

  val baseCegarConfig = baseConfig.backendConfig.specConfig!!
  val verifiedProperty = baseConfig.inputConfig.property.verifiedProperty
  val multiThreadedCegarConfig =
    baseCegarConfig.copy(
      coi = if (verifiedProperty == ERROR_LOCATION) COI else NO_COI,
      por = if (verifiedProperty == ERROR_LOCATION) AASPOR else SPOR,
      abstractorConfig = baseCegarConfig.abstractorConfig.copy(search = DFS),
    )
  baseConfig =
    baseConfig.copy(
      backendConfig = baseConfig.backendConfig.copy(specConfig = multiThreadedCegarConfig)
    )

  fun getStm(inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()

    val cegarXcfa =
      xcfa.optimizeFurther(
        ProcedurePassManager(
          listOf(
            LbePass(parseContext, LBE_LOCAL),
            NormalizePass(),
            DeterministicPass(),
            UnusedVarPass(logger, portfolioConfig.inputConfig.property),
            EmptyEdgeRemovalPass(),
            UnusedLocRemovalPass(),
          )
        )
      )

    val property = baseConfig.inputConfig.property.copy()
    val ocXcfa =
      if (baseConfig.inputConfig.property.verifiedProperty == DATA_RACE)
        xcfa.optimizeFurther(
          ProcedurePassManager(listOf(DataRaceToReachabilityPass(property, true)))
        )
      else xcfa

    val multithreadCegarBaseConfig =
      baseConfig.copy(
        inputConfig =
          baseConfig.inputConfig.copy(
            xcfaWCtx =
              if (portfolioConfig.backendConfig.parseInProcess) null
              else Triple(cegarXcfa, mcm, parseContext)
          ),
        frontendConfig = baseConfig.frontendConfig.copy(lbeLevel = LBE_LOCAL),
      )

    val ocBaseConfig =
      XcfaConfig(
        inputConfig =
          baseConfig.inputConfig.copy(
            xcfaWCtx = Triple(ocXcfa, mcm, parseContext),
            property = property,
          ),
        frontendConfig =
          baseConfig.frontendConfig.copy(
            lbeLevel = NO_LBE,
            enableDataRaceToReachability =
              baseConfig.inputConfig.property.verifiedProperty == DATA_RACE,
          ),
        backendConfig =
          BackendConfig(
            backend = OC,
            solverHome = baseConfig.backendConfig.solverHome,
            inProcess = inProcess,
            parseInProcess = inProcess && portfolioConfig.backendConfig.parseInProcess,
            specConfig = OcConfig(decisionProcedure = OcDecisionProcedureType.BASIC),
          ),
        outputConfig = baseConfig.outputConfig,
        debugConfig = baseConfig.debugConfig,
      )

    val config_OC =
      ConfigNode(
        "MULTITHREAD_OC_BASIC_GENERIC3-$inProcess",
        ocBaseConfig.copy(
          backendConfig =
            ocBaseConfig.backendConfig.copy(
              timeoutMs = 250_000,
              specConfig =
                OcConfig(
                  decisionProcedure = OcDecisionProcedureType.BASIC,
                  autoConflict = AutoConflictFinderConfig.GENERIC,
                  autoConflictBound = 3,
                ),
            )
        ),
        checker,
      )

    val config_MULTITHREAD_EXPL_SEQ_ITP =
      ConfigNode(
        "MULTITHREAD_EXPL_SEQ_ITP-$inProcess",
        multithreadCegarBaseConfig.adaptConfig(
          inProcess = inProcess,
          domain = EXPL,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = SEQ_ITP,
          timeoutMs = 300_000,
        ),
        checker,
      )

    val config_MULTITHREAD_PRED_BW_BIN_ITP_ALLASSUMES =
      ConfigNode(
        "MULTITHREAD_PRED_BW_BIN_ITP_ALLASSUMES-$inProcess",
        multithreadCegarBaseConfig.adaptConfig(
          inProcess = inProcess,
          domain = PRED_CART,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = BW_BIN_ITP,
          initPrec = ALLASSUMES,
          timeoutMs = 320_000,
        ),
        checker,
      )

    val config_MULTITHREAD_PRED_SEQ_ITP_NEWZ3 =
      ConfigNode(
        "MULTITHREAD_PRED_SEQ_ITP_NEWZ3-$inProcess",
        multithreadCegarBaseConfig.adaptConfig(
          inProcess = inProcess,
          domain = PRED_CART,
          abstractionSolver = "Z3:4.13",
          refinementSolver = "Z3:4.13",
          refinement = SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )

    val config_MULTITHREAD_EXPL_NWT_IT_WP_MATHSAT =
      ConfigNode(
        "MULTITHREAD_EXPL_NWT_WP_MATHSAT-$inProcess",
        multithreadCegarBaseConfig.adaptConfig(
          inProcess = inProcess,
          domain = EXPL,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = NWT_IT_WP,
          timeoutMs = 0,
        ),
        checker,
      )

    val startNode =
      when (baseConfig.inputConfig.property.verifiedProperty) {
        ERROR_LOCATION -> {
          val config_MULTITHREAD_EXPL_COI_SEQ_ITP =
            ConfigNode(
              "MULTITHREAD_EXPL_COI_SEQ_ITP-$inProcess",
              multithreadCegarBaseConfig.adaptConfig(
                inProcess = inProcess,
                domain = EXPL,
                abstractionSolver = "Z3",
                refinementSolver = "Z3",
                refinement = SEQ_ITP,
                coi = COI,
                timeoutMs = 250_000,
              ),
              checker,
            )

          val config_MULTITHREAD_PRED_COI_SEQ_ITP_ALLASSUMES =
            ConfigNode(
              "MULTITHREAD_PRED_COI_SEQ_ITP_ALLASSUMES-$inProcess",
              multithreadCegarBaseConfig.adaptConfig(
                inProcess = inProcess,
                domain = PRED_CART,
                abstractionSolver = "Z3",
                refinementSolver = "Z3",
                refinement = SEQ_ITP,
                coi = COI,
                initPrec = ALLASSUMES,
                timeoutMs = 0,
              ),
              checker,
            )

          val config_MULTITHREAD_PRED_COI_SEQ_ITP_NEWZ3 =
            ConfigNode(
              "MULTITHREAD_PRED_COI_SEQ_ITP_NEWZ3-$inProcess",
              multithreadCegarBaseConfig.adaptConfig(
                inProcess = inProcess,
                domain = PRED_CART,
                abstractionSolver = "Z3:4.13",
                refinementSolver = "Z3:4.13",
                refinement = SEQ_ITP,
                coi = COI,
                timeoutMs = 0,
              ),
              checker,
            )

          edges.add(Edge(config_OC, config_MULTITHREAD_EXPL_COI_SEQ_ITP, anyError))

          edges.add(
            Edge(
              config_MULTITHREAD_EXPL_COI_SEQ_ITP,
              config_MULTITHREAD_PRED_BW_BIN_ITP_ALLASSUMES,
              anyError,
            )
          )

          edges.add(
            Edge(
              config_MULTITHREAD_PRED_BW_BIN_ITP_ALLASSUMES,
              config_MULTITHREAD_PRED_COI_SEQ_ITP_ALLASSUMES,
              anyError,
            )
          )

          edges.add(
            Edge(
              config_MULTITHREAD_PRED_COI_SEQ_ITP_ALLASSUMES,
              config_MULTITHREAD_PRED_COI_SEQ_ITP_NEWZ3,
              anyError,
            )
          )

          config_OC
        }

        DATA_RACE -> {
          val config_MULTITHREAD_PRED_SEQ_ITP =
            ConfigNode(
              "MULTITHREAD_PRED_SEQ_ITP-$inProcess",
              multithreadCegarBaseConfig.adaptConfig(
                inProcess = inProcess,
                domain = PRED_CART,
                abstractionSolver = "Z3",
                refinementSolver = "Z3",
                refinement = SEQ_ITP,
                timeoutMs = 750_000,
              ),
              checker,
            )

          val config_OC_NO_CONFLICT = ConfigNode("MULTITHREAD_OC-$inProcess", ocBaseConfig, checker)

          edges.add(Edge(config_MULTITHREAD_PRED_SEQ_ITP, config_OC_NO_CONFLICT, anyError))

          config_MULTITHREAD_PRED_SEQ_ITP
        }

        else -> {
          val config_MULTITHREAD_PRED_SEQ_ITP =
            ConfigNode(
              "MULTITHREAD_PRED_SEQ_ITP-$inProcess",
              multithreadCegarBaseConfig.adaptConfig(
                inProcess = inProcess,
                domain = PRED_CART,
                abstractionSolver = "Z3",
                refinementSolver = "Z3",
                refinement = SEQ_ITP,
                timeoutMs = 0,
              ),
              checker,
            )

          edges.add(
            Edge(config_MULTITHREAD_EXPL_SEQ_ITP, config_MULTITHREAD_PRED_SEQ_ITP, anyError)
          )

          edges.add(
            Edge(
              config_MULTITHREAD_PRED_SEQ_ITP,
              config_MULTITHREAD_PRED_BW_BIN_ITP_ALLASSUMES,
              anyError,
            )
          )

          edges.add(
            Edge(
              config_MULTITHREAD_PRED_BW_BIN_ITP_ALLASSUMES,
              config_MULTITHREAD_PRED_SEQ_ITP_NEWZ3,
              anyError,
            )
          )

          edges.add(
            Edge(
              config_MULTITHREAD_PRED_SEQ_ITP_NEWZ3,
              config_MULTITHREAD_EXPL_NWT_IT_WP_MATHSAT,
              anyError,
            )
          )

          config_MULTITHREAD_EXPL_SEQ_ITP
        }
      }

    return STM(startNode, edges)
  }

  logger.benchmark("Using portfolio: MULTITHREAD\n")

  if (portfolioConfig.debugConfig.debug) {
    return getStm(false)
  }

  val inProcessStm = getStm(true)
  val notInProcessStm = getStm(false)
  val inProcess = HierarchicalNode("InProcess", inProcessStm)
  val notInProcess = HierarchicalNode("NotInprocess", notInProcessStm)
  val fallbackEdge = Edge(inProcess, notInProcess, anyError)

  return STM(inProcess, setOf(fallbackEdge))
}
