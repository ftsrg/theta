/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.ErrorDetection.DATA_RACE
import hu.bme.mit.theta.xcfa.ErrorDetection.ERROR_LOCATION
import hu.bme.mit.theta.xcfa.ErrorDetection.MEMCLEANUP
import hu.bme.mit.theta.xcfa.ErrorDetection.MEMSAFETY
import hu.bme.mit.theta.xcfa.ErrorDetection.OVERFLOW
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
import hu.bme.mit.theta.xcfa.passes.LbePass.LbeLevel.LBE_LOCAL
import hu.bme.mit.theta.xcfa.passes.LbePass.LbeLevel.NO_LBE

private const val YICES = "JavaSMT:YICES2"

private val anythingButTimeout =
  ExceptionTrigger(
    fallthroughExceptions = setOf(ErrorCodeException(ExitCodes.TIMEOUT.code)),
    label = "AnythingButTimeout",
  )

/**
 * The SV-COMP 2027 multithreaded portfolio. It differs from [multithreadPortfolio] in its OC
 * configurations, chosen on the ConcurrencySafety category: OC time slices lead the reachability,
 * data race and overflow chains.
 */
@Suppress("LocalVariableName")
fun multithreadPortfolio27(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {

  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  var baseConfig: XcfaConfig<CFrontendConfig, CegarConfig> =
    baseCegarConfig(xcfa, parseContext, portfolioConfig) as XcfaConfig<CFrontendConfig, CegarConfig>

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

    val multithreadCegarBaseConfig =
      baseConfig.copy(
        inputConfig = baseConfig.inputConfig.copy(xcfaWCtx = null),
        frontendConfig = baseConfig.frontendConfig.copy(lbeLevel = LBE_LOCAL),
      )

    /**
     * An OC configuration as measured on the ConcurrencySafety category, with an explicit
     * arithmetic and memory model, so the program is re-read rather than reusing the portfolio's
     * encoding. Data races are checked natively, which needs IDL. No LBE: an edge is one atomic
     * unit for OC (and `LbePass` disables non-local LBE for multithreaded programs anyway).
     */
    fun oc(
      solver: String,
      decisionProcedure: OcDecisionProcedureType,
      memoryModel: MemoryModelType,
      timeoutMs: Long,
      arithmetic: ArithmeticType = ArithmeticType.bitvector,
      ptrSizeInMemory: Boolean = false,
    ): ConfigNode {
      val solverName = solver.substringAfter(':').lowercase()
      val name =
        "MULTITHREAD_OC_${decisionProcedure}_${arithmetic}_${memoryModel}_$solverName-$inProcess"
      return ConfigNode(
        name,
        XcfaConfig(
          inputConfig = baseConfig.inputConfig.copy(xcfaWCtx = null),
          frontendConfig =
            baseConfig.frontendConfig.copy(
              lbeLevel = NO_LBE,
              enableDataRaceToReachability = false,
              ptrSizeInMemory = ptrSizeInMemory,
              // a fresh instance per node: the frontend rewrites the memory model on its fallbacks
              specConfig =
                (baseConfig.frontendConfig.specConfig ?: CFrontendConfig()).copy(
                  arithmetic = arithmetic,
                  memoryModel = memoryModel,
                ),
            ),
          backendConfig =
            BackendConfig(
              backend = OC,
              solverHome = baseConfig.backendConfig.solverHome,
              inProcess = inProcess,
              timeoutMs = timeoutMs,
              specConfig =
                OcConfig(
                  decisionProcedure = decisionProcedure,
                  autoConflict = AutoConflictFinderConfig.SIMPLE,
                  forceUnrollBoundStart = 1,
                  smtSolver = solver,
                ),
            ),
          outputConfig = baseConfig.outputConfig,
          debugConfig = baseConfig.debugConfig,
        ),
        checker,
      )
    }

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
          abstractionSolver = portfolioConfig.solverVersionOrLatestFallback("mathsat", "5.6.10"),
          refinementSolver = portfolioConfig.solverVersionOrLatestFallback("mathsat", "5.6.10"),
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

          // Overflows arrive here as reachability of the instrumented checks. The propagator is
          // used only for them: on plain reachability it missed bugs, on overflows it gave no wrong
          // verdict with integer arithmetic or with bitvectors under multi.
          val config_OC =
            if (baseConfig.inputConfig.property.inputProperty == OVERFLOW) {
              val config_OC_PROP_INT =
                oc(
                  "Z3:new",
                  OcDecisionProcedureType.PROPAGATOR,
                  MemoryModelType.flat,
                  100_000,
                  ArithmeticType.integer,
                )
              // The propagator gives up on programs whose reads are matched across addresses.
              val config_OC_IDL =
                oc(YICES, OcDecisionProcedureType.IDL, MemoryModelType.multi, 80_000)
              val config_OC_IDL_FLAT =
                oc(YICES, OcDecisionProcedureType.IDL, MemoryModelType.flat, 740_000)
              edges.add(Edge(config_OC_PROP_INT, config_OC_IDL, anyError))
              val config_OC_Z3 =
                oc("Z3:new", OcDecisionProcedureType.IDL, MemoryModelType.flat, 300_000)
              edges.add(Edge(config_OC_IDL, config_OC_IDL_FLAT, anyError))
              // the first matching edge is taken, so the non-timeout edge goes first
              edges.add(Edge(config_OC_IDL_FLAT, config_OC_Z3, anythingButTimeout))
              edges.add(Edge(config_OC_IDL_FLAT, config_MULTITHREAD_EXPL_COI_SEQ_ITP, anyError))
              edges.add(Edge(config_OC_Z3, config_MULTITHREAD_EXPL_COI_SEQ_ITP, anyError))
              config_OC_PROP_INT
            } else if (
              baseConfig.inputConfig.property.inputProperty in setOf(MEMSAFETY, MEMCLEANUP)
            ) {
              val config_OC_MEM_YICES =
                oc(
                  YICES,
                  OcDecisionProcedureType.IDL,
                  MemoryModelType.multi,
                  150_000,
                  ptrSizeInMemory = true,
                )
              // Under flat, checks over static objects need no ghost state, see MemsafetyPass.
              val config_OC_MEM_FLAT =
                oc(
                  YICES,
                  OcDecisionProcedureType.IDL,
                  MemoryModelType.flat,
                  600_000,
                  ptrSizeInMemory = true,
                )
              val config_OC_MEM =
                oc("Z3:new", OcDecisionProcedureType.IDL, MemoryModelType.multi, 100_000)
              edges.add(Edge(config_OC_MEM_YICES, config_OC_MEM_FLAT, anyError))
              edges.add(Edge(config_OC_MEM_FLAT, config_OC_MEM, anyError))
              edges.add(Edge(config_OC_MEM, config_MULTITHREAD_EXPL_COI_SEQ_ITP, anyError))
              config_OC_MEM_YICES
            } else {
              // Addresses are only known to be disjoint under the multi memory model, which removes
              // read-from candidates, but it rejects some pointer arithmetic, which flat encodes.
              val config_OC_MULTI =
                oc(YICES, OcDecisionProcedureType.IDL, MemoryModelType.multi, 60_000)
              val config_OC_YICES =
                oc(YICES, OcDecisionProcedureType.IDL, MemoryModelType.flat, 740_000)
              val config_OC_Z3 =
                oc("Z3:new", OcDecisionProcedureType.IDL, MemoryModelType.flat, 400_000)
              edges.add(Edge(config_OC_MULTI, config_OC_YICES, anyError))
              // yices has no arrays, which symbolic mutexes need; the non-timeout edge goes first
              edges.add(Edge(config_OC_YICES, config_OC_Z3, anythingButTimeout))
              edges.add(Edge(config_OC_YICES, config_MULTITHREAD_EXPL_COI_SEQ_ITP, anyError))
              edges.add(Edge(config_OC_Z3, config_MULTITHREAD_EXPL_COI_SEQ_ITP, anyError))
              config_OC_MULTI
            }

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
                timeoutMs = 0,
              ),
              checker,
            )

          if (ArithmeticTrait.ARR in parseContext.arithmeticTraits) {
            val config_OC_MULTI =
              oc(YICES, OcDecisionProcedureType.IDL, MemoryModelType.multi, 60_000)
            val config_OC_FLAT =
              oc(YICES, OcDecisionProcedureType.IDL, MemoryModelType.flat, 740_000)
            // yices has no arrays, which symbolic mutexes need
            val config_OC_FLAT_Z3 =
              oc("Z3:new", OcDecisionProcedureType.IDL, MemoryModelType.flat, 300_000)
            // Only reached when the flat slices failed for a reason other than time, mostly the
            // frontend rejecting the program: the byte-level memory model encodes some of those.
            val config_OC_BYTES =
              oc("Z3:new", OcDecisionProcedureType.IDL, MemoryModelType.bytes, 100_000)

            edges.add(Edge(config_OC_MULTI, config_OC_FLAT, anyError))
            // the first matching edge is taken, so the non-timeout edge goes first
            edges.add(Edge(config_OC_FLAT, config_OC_FLAT_Z3, anythingButTimeout))
            edges.add(Edge(config_OC_FLAT, config_MULTITHREAD_PRED_SEQ_ITP, anyError))
            edges.add(Edge(config_OC_FLAT_Z3, config_OC_BYTES, anythingButTimeout))
            edges.add(Edge(config_OC_FLAT_Z3, config_MULTITHREAD_PRED_SEQ_ITP, anyError))
            edges.add(Edge(config_OC_BYTES, config_MULTITHREAD_PRED_SEQ_ITP, anyError))

            config_OC_MULTI
          } else {
            val config_OC_MULTI =
              oc(YICES, OcDecisionProcedureType.IDL, MemoryModelType.multi, 100_000)
            val config_OC_FLAT =
              oc("Z3:new", OcDecisionProcedureType.IDL, MemoryModelType.flat, 100_000)
            // Only reached when the flat slice failed for a reason other than time, mostly the
            // frontend rejecting the program: the byte-level memory model encodes some of those.
            val config_OC_BYTES =
              oc("Z3:new", OcDecisionProcedureType.IDL, MemoryModelType.bytes, 100_000)

            edges.add(Edge(config_OC_MULTI, config_OC_FLAT, anyError))
            // the first matching edge is taken, so the non-timeout edge goes first
            edges.add(Edge(config_OC_FLAT, config_OC_BYTES, anythingButTimeout))
            edges.add(Edge(config_OC_FLAT, config_MULTITHREAD_PRED_SEQ_ITP, anyError))
            edges.add(Edge(config_OC_BYTES, config_MULTITHREAD_PRED_SEQ_ITP, anyError))

            config_OC_MULTI
          }
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

  logger.benchmark("Using portfolio: MULTITHREAD27\n")

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
