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

import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.params.Domain.*
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.ARR
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.BITWISE
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.FLOAT
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.LIN_INT
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.MULTITHREAD
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.NONLIN_INT
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.PTR
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.dereferences

fun emergent26(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {
  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  var baseCegarConfig = baseCegarConfig(xcfa, mcm, parseContext, portfolioConfig, false)
  val baseBoundedConfig = baseBoundedConfig(xcfa, mcm, parseContext, portfolioConfig, false)
  val baseMddConfig = baseMddConfig(xcfa, mcm, parseContext, portfolioConfig, false)
  val baseIc3Config = baseIc3Config(xcfa, mcm, parseContext, portfolioConfig, false)

  if (parseContext.multiThreading) {
//    val baseSpecConfig = baseCegarConfig.backendConfig.specConfig!!
//    val verifiedProperty = baseCegarConfig.inputConfig.property.verifiedProperty
//    val multiThreadedSpecConfig =
//      baseSpecConfig.copy(
//        coi = if (verifiedProperty == ErrorDetection.ERROR_LOCATION) ConeOfInfluenceMode.COI else ConeOfInfluenceMode.NO_COI,
//        por = if (verifiedProperty == ErrorDetection.ERROR_LOCATION) POR.AASPOR else POR.SPOR,
//        abstractorConfig = baseSpecConfig.abstractorConfig.copy(search = Search.DFS),
//      )
//    baseCegarConfig =
//      baseCegarConfig.copy(
//        backendConfig = baseCegarConfig.backendConfig.copy(specConfig = multiThreadedSpecConfig)
//      )
  }

  fun getStm(mainTrait: MainTrait, inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()

    fun cegar (timeout: Long, solver: String, domain: Domain = Domain.PRED_CART, refinement: Refinement = Refinement.SEQ_ITP): ConfigNode {
      return ConfigNode(
        "${domain.name}-${refinement.name}-$inProcess",
        baseCegarConfig.adaptConfig(
          inProcess = inProcess,
          domain = domain,
          refinement = refinement,
          exprSplitter = ExprSplitterOptions.WHOLE,
          timeoutMs = timeout,
          abstractionSolver = solver,
          refinementSolver = solver,
        ),
        checker,
      )
    }

    val bmc = { timeout: Long, solver: String ->
      ConfigNode(
        "BMC-$inProcess",
        baseBoundedConfig.adaptConfig(
          inProcess = inProcess,
          bmcEnabled = true,
          indEnabled = false,
          itpEnabled = false,
          timeoutMs = timeout,
          bmcSolver = solver,
        ),
        checker,
      )
    }

    val kind = { timeout: Long, solver: String ->
      ConfigNode(
        "KIND-$inProcess",
        baseBoundedConfig.adaptConfig(
          inProcess = inProcess,
          bmcEnabled = true,
          indEnabled = true,
          itpEnabled = false,
          timeoutMs = timeout,
          bmcSolver = solver,
          indSolver = solver,
        ),
        checker,
      )
    }

    val imc = { timeout: Long, solver: String ->
      ConfigNode(
        "IMC-$inProcess",
        baseBoundedConfig.adaptConfig(
          inProcess = inProcess,
          bmcEnabled = false,
          indEnabled = false,
          itpEnabled = true,
          timeoutMs = timeout,
          itpSolver = solver,
        ),
        checker,
      )
    }

    val ic3 = { timeout: Long, solver: String ->
      ConfigNode(
        "IC3-$inProcess",
        baseIc3Config.copy(
          backendConfig = baseIc3Config.backendConfig.copy(
            parseInProcess = true,
            timeoutMs = timeout,
            inProcess = inProcess,
            specConfig = baseIc3Config.backendConfig.specConfig!!.copy(solver = solver, reversed = true),
          )
        ),
        checker,
      )
    }

    val ic3Cegar = { timeout: Long, solver: String ->
      ConfigNode(
        "IC3-cegar-$inProcess",
        baseIc3Config.copy(
          backendConfig = baseIc3Config.backendConfig.copy(
            parseInProcess = true,
            timeoutMs = timeout,
            inProcess = inProcess,
            specConfig = baseIc3Config.backendConfig.specConfig!!.copy(solver = solver, cegar = true, reversed = true),
          )
        ),
        checker,
      )
    }

    val mdd = { timeout: Long, solver: String ->
      ConfigNode(
        "MDD-$inProcess",
        baseMddConfig.copy(
          backendConfig =
            baseMddConfig.backendConfig.copy(
              timeoutMs = timeout,
              inProcess = inProcess,
              parseInProcess = true,
              specConfig = baseMddConfig.backendConfig.specConfig!!.copy(solver = solver)
            )
        ),
        checker,
      )
    }

    val mddCegar = { timeout: Long, solver: String ->
      ConfigNode(
        "MDD-cegar-$inProcess",
        baseMddConfig.copy(
          backendConfig =
            baseMddConfig.backendConfig.copy(
              timeoutMs = timeout,
              inProcess = inProcess,
              parseInProcess = true,
              specConfig = baseMddConfig.backendConfig.specConfig!!.copy(cegar = true, solver = solver),
            ),
        ),
        checker,
      )
    }

    val complex =
      ConfigNode(
        "Complex-$inProcess",
        XcfaConfig(
          inputConfig =
            portfolioConfig.inputConfig.copy(
              xcfaWCtx =
                if (portfolioConfig.backendConfig.parseInProcess) null
                else Triple(xcfa, mcm, parseContext),
              propertyFile = null,
              property = portfolioConfig.inputConfig.property,
            ),
          frontendConfig = portfolioConfig.frontendConfig,
          backendConfig =
            (portfolioConfig.backendConfig as BackendConfig<PortfolioConfig>).copy(
              specConfig = PortfolioConfig("COMPLEX")
            ),
          outputConfig = baseCegarConfig.outputConfig,
          debugConfig = portfolioConfig.debugConfig,
        ),
        checker,
      )

    val types = xcfa.collectVars().map { it.type }.toSet()

    infix fun ConfigNode.then(node: ConfigNode): ConfigNode {
      edges.add(Edge(this, node, if (inProcess) timeoutOrNotSolvableError else anyError))
      return node
    }

    infix fun ConfigNode.onSolverError(node: ConfigNode): ConfigNode {
      edges.add(Edge(this, node, solverError))
      return node
    }

    val (startingConfig, endConfig) =
      if (xcfa.isInlined) {
        when (mainTrait) {

          BITWISE, // TODO

          FLOAT -> {

            val expl_pred_nwtCVC = cegar(200_000, "cvc5:1.2.0", Domain.EXPL_PRED_STMT, Refinement.NWT_IT_WP)
            val expl_pred_seqCVC = cegar(200_000, "cvc5:1.2.0", Domain.EXPL_PRED_STMT, Refinement.SEQ_ITP)
            val ic3CVC = ic3(100_000, "cvc5:1.2.0")
            val ic3CegarCVC = ic3Cegar(100_000, "cvc5:1.2.0")
            val mddCegarCVC = mddCegar(100_000, "cvc5:1.2.0")

            val expl_pred_nwt = cegar(200_000, "Z3", Domain.EXPL_PRED_STMT, Refinement.NWT_IT_WP)
            val expl_pred_seq = cegar(200_000, "Z3", Domain.EXPL_PRED_STMT, Refinement.SEQ_ITP)
            val ic3 = ic3(100_000, "Z3")
            val ic3Cegar = ic3Cegar(100_000, "Z3")
            val mddCegar = mddCegar(100_000, "Z3")

            expl_pred_nwtCVC then
              expl_pred_seqCVC then
              ic3CVC then
              ic3CegarCVC then
              mddCegarCVC

            expl_pred_nwtCVC onSolverError expl_pred_nwt
            expl_pred_seqCVC onSolverError expl_pred_seq
            ic3CVC onSolverError ic3
            ic3CegarCVC onSolverError ic3Cegar
            mddCegarCVC onSolverError mddCegar

            expl_pred_nwt then
              expl_pred_seq then
              ic3 then
              ic3Cegar then
              mddCegar then complex

            expl_pred_nwtCVC to mddCegarCVC
          }

          LIN_INT -> {

            val expl_pred_nwtMS = cegar(200_000, "mathsat:5.6.12", Domain.EXPL_PRED_STMT, Refinement.NWT_IT_WP)
            val expl_pred_seqMS = cegar(200_000, "mathsat:5.6.12", Domain.EXPL_PRED_STMT, Refinement.SEQ_ITP)
            val ic3MS = ic3(100_000, "mathsat:5.6.12")
            val ic3CegarMS = ic3Cegar(100_000, "mathsat:5.6.12")
            val mddCegarMS = mddCegar(100_000, "mathsat:5.6.12")

            val expl_pred_nwt = cegar(200_000, "Z3", Domain.EXPL_PRED_STMT, Refinement.NWT_IT_WP)
            val expl_pred_seq = cegar(200_000, "Z3", Domain.EXPL_PRED_STMT, Refinement.SEQ_ITP)
            val ic3 = ic3(100_000, "Z3")
            val ic3Cegar = ic3Cegar(100_000, "Z3")
            val mddCegar = mddCegar(100_000, "Z3")

            expl_pred_nwtMS then
              expl_pred_seqMS then
              ic3MS then
              ic3CegarMS then
              mddCegarMS

            expl_pred_nwtMS onSolverError expl_pred_nwt
            expl_pred_seqMS onSolverError expl_pred_seq
            ic3MS onSolverError ic3
            ic3CegarMS onSolverError ic3Cegar
            mddCegarMS onSolverError mddCegar

            expl_pred_nwt then
              expl_pred_seq then
              ic3 then
              ic3Cegar then
              mddCegar then complex

            expl_pred_nwtMS to mddCegarMS
          }

          NONLIN_INT, // TODO

          ARR, // TODO

          MULTITHREAD -> {

            val mdd = mdd(600_000, "Z3")
            val bmc = bmc(150_000, "Z3")
            val kind = kind(150_000, "Z3")

            val mddMS = mdd(600_000, "mathsat:5.6.12")
            val bmcMS = bmc(150_000, "mathsat:5.6.12")
            val kindMS = kind(150_000, "mathsat:5.6.12")

            mdd then
              bmc then
              kind

            mdd onSolverError mddMS
            bmc onSolverError bmcMS
            kind onSolverError kindMS

            mddMS then
              bmcMS then
              kindMS then complex

            mdd to kind

          }

          PTR -> {
            // TODO
            val expl_pred_nwt = cegar(150_000, "Z3", Domain.EXPL_PRED_STMT, Refinement.NWT_IT_WP)
            val expl_pred_seq = cegar(150_000, "Z3", Domain.EXPL_PRED_STMT, Refinement.SEQ_ITP)
            val ic3 = ic3(150_000, "Z3")
            val ic3Cegar = ic3Cegar(150_000, "Z3")
            val mddCegar = mddCegar(100_000, "Z3")
            val expl_pred_nwtMS = cegar(150_000, "mathsat:5.6.12", Domain.EXPL_PRED_STMT, Refinement.NWT_IT_WP)
            val expl_pred_seqMS = cegar(150_000, "mathsat:5.6.12", Domain.EXPL_PRED_STMT, Refinement.SEQ_ITP)
            val ic3MS = ic3(150_000, "mathsat:5.6.12")
            val ic3CegarMS = ic3Cegar(150_000, "mathsat:5.6.12")
            val mddCegarMS = mddCegar(100_000, "mathsat:5.6.12")

            expl_pred_nwtMS then
              expl_pred_seqMS then
              ic3MS then
              ic3CegarMS then
              mddCegarMS

            expl_pred_nwtMS onSolverError expl_pred_nwt
            expl_pred_seqMS onSolverError expl_pred_seq
            ic3MS onSolverError ic3
            ic3CegarMS onSolverError ic3Cegar
            mddCegarMS onSolverError mddCegar

            expl_pred_nwt then
              expl_pred_seq then
              ic3 then
              ic3Cegar then
              mddCegar then complex

            expl_pred_nwtMS to mddCegarMS
          }

        }
      } else {
        val baseSpecConfig = baseCegarConfig.backendConfig.specConfig!!
        val recursiveConfig =
          baseSpecConfig.copy(
            abstractorConfig = baseSpecConfig.abstractorConfig.copy(search = Search.BFS),
            refinerConfig = baseSpecConfig.refinerConfig.copy(pruneStrategy = PruneStrategy.LAZY),
          )
        baseCegarConfig =
          baseCegarConfig.copy(backendConfig = baseCegarConfig.backendConfig.copy(specConfig = recursiveConfig))

        val expl_pred_nwt = cegar(150_000, "Z3", Domain.EXPL_PRED_STMT, Refinement.NWT_IT_WP)
        val expl_pred_seq = cegar(150_000, "Z3", Domain.EXPL_PRED_STMT, Refinement.SEQ_ITP)
        val expl_pred_nwtMS = cegar(150_000, "mathsat:5.6.12", Domain.EXPL_PRED_STMT, Refinement.NWT_IT_WP)
        val expl_pred_seqMS = cegar(150_000, "mathsat:5.6.12", Domain.EXPL_PRED_STMT, Refinement.SEQ_ITP)

        expl_pred_nwtMS then
          expl_pred_seqMS

        expl_pred_nwtMS onSolverError expl_pred_nwt
        expl_pred_seqMS onSolverError expl_pred_seq

        expl_pred_nwt then
          expl_pred_seq then complex

        expl_pred_nwtMS to expl_pred_seqMS
      }

    endConfig then complex

    return STM(startingConfig, edges)
  }

  val mainTrait =
    when {
      parseContext.multiThreading -> MULTITHREAD
      xcfa.procedures.any { p -> p.edges.any { it.label.dereferences.isNotEmpty() } } -> PTR
      ArithmeticTrait.FLOAT in parseContext.arithmeticTraits -> FLOAT
      ArithmeticTrait.ARR in parseContext.arithmeticTraits -> ARR
      ArithmeticTrait.BITWISE in parseContext.arithmeticTraits -> BITWISE
      ArithmeticTrait.NONLIN_INT in parseContext.arithmeticTraits -> NONLIN_INT
      else -> LIN_INT
    }

  val inProcessStm = getStm(mainTrait, true)
  val notInProcessStm = getStm(mainTrait, false)

  val inProcess = HierarchicalNode("InProcess", inProcessStm)
  val notInProcess = HierarchicalNode("NotInprocess", notInProcessStm)

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(mainTrait,false)
  else STM(inProcess, setOf(fallbackEdge))
}
