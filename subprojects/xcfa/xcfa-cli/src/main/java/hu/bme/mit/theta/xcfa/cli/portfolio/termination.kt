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
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.params.Domain.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.model.XCFA

fun termination(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {
  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  val baseAsgCegarConfig = baseAsgCegarConfig(xcfa, mcm, parseContext, portfolioConfig, false)
  val baseBoundedConfig = baseBoundedConfig(xcfa, mcm, parseContext, portfolioConfig, false)

  fun getStm(inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()

    val expl = { timeout: Long, solver: String ->
      ConfigNode(
        "ASGCEGAR-EXPL-$inProcess",
        baseAsgCegarConfig.adaptConfig(
          refinementSolver = solver,
          abstractionSolver = solver,
          domain = EXPL,
          inProcess = inProcess,
          timeoutMs = timeout,
          initPrec = InitPrec.ALLVARS,
        ),
        checker,
      )
    }

    val predcart = { timeout: Long, solver: String ->
      ConfigNode(
        "ASGCEGAR-PREDCART-$inProcess",
        baseAsgCegarConfig.adaptConfig(
          refinementSolver = solver,
          abstractionSolver = solver,
          domain = PRED_CART,
          inProcess = inProcess,
          timeoutMs = timeout,
        ),
        checker,
      )
    }

    val predbool = { timeout: Long, solver: String ->
      ConfigNode(
        "ASGCEGAR-PREDBOOL-$inProcess",
        baseAsgCegarConfig.adaptConfig(
          refinementSolver = solver,
          abstractionSolver = solver,
          domain = PRED_BOOL,
          inProcess = inProcess,
          timeoutMs = timeout,
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

    val types = xcfa.collectVars().map { it.type }.toSet()

    infix fun ConfigNode.then(node: ConfigNode): ConfigNode {
      edges.add(Edge(this, node, if (inProcess) anythingButServerError else anyError))
      return node
    }

    infix fun List<ConfigNode>.then(node: ConfigNode): ConfigNode {
      forEach { it then node }
      return node
    }

    infix fun ConfigNode.or(node: ConfigNode): List<ConfigNode> {
      edges.add(Edge(this, node, solverError))
      return listOf(this, node)
    }

    val (startingConfig: ConfigNode, endConfig: ConfigNode) =
      if (xcfa.isInlined) {
        if (types.any { it is BvType }) {
          val expl = expl(100_000, "cvc5:1.0.8")
          val predcart = predcart(100_000, "cvc5:1.0.8")
          val predbool = predbool(100_000, "cvc5:1.0.8")
          val bmc = bmc(100_000, "Z3:4.13")
          val kind = kind(300_000, "Z3:4.13")
          val imcCVC5 = imc(300_000, "cvc5:1.0.8")
          val imcMathSAT = imc(300_000, "mathsat:5.6.10")
          val kindMathSAT = kind(300_000, "mathsat:5.6.10")

          expl then
            predcart then
            predbool then
            bmc then
            kind then
            imcCVC5 then
            imcMathSAT then
            kindMathSAT

          Pair(expl, kindMathSAT)
        } else if (types.any { it is FpType }) {
          val expl = expl(100_000, "cvc5:1.0.8")
          val predcart = predcart(100_000, "cvc5:1.0.8")
          val predbool = predbool(100_000, "cvc5:1.0.8")
          val bmcCVC5 = bmc(100_000, "cvc5:1.0.8")
          val kindCVC5 = kind(300_000, "cvc5:1.0.8")
          val imcCVC5 = imc(300_000, "cvc5:1.0.8")
          val imcMathSAT = imc(300_000, "mathsat:5.6.10")
          val kindMathSAT = kind(300_000, "mathsat:5.6.10")

          expl then
            predcart then
            predbool then
            bmcCVC5 then
            kindCVC5 then
            imcCVC5 then
            imcMathSAT then
            kindMathSAT

          Pair(expl, kindMathSAT)
        } else if (types.any { it is ArrayType<*, *> }) {
          val expl = expl(100_000, "Z3:4.13")
          val predcart = predcart(100_000, "Z3:4.13")
          val predbool = predbool(100_000, "Z3:4.13")
          val bmc = bmc(100_000, "Z3:4.13")
          val bmcLegacy = bmc(100_000, "Z3")
          val kind = kind(300_000, "Z3:4.13")
          val kindLegacy = kind(300_000, "Z3")
          val imcCVC5 = imc(300_000, "cvc5:1.0.8")
          val imcMathSAT = imc(300_000, "mathsat:5.6.10")
          val kindMathSAT = kind(300_000, "mathsat:5.6.10")

          (bmc or bmcLegacy) then
            (kind or kindLegacy).first() then
            expl then
            predcart then
            predbool then
            imcCVC5 then
            imcMathSAT then
            kindMathSAT

          Pair(bmc, kindMathSAT)
        } else {
          val expl = expl(100_000, "Z3:4.13")
          val predcart = predcart(100_000, "Z3:4.13")
          val predbool = predbool(100_000, "Z3:4.13")
          val bmc = bmc(100_000, "Z3:4.13")
          val kind = kind(300_000, "Z3:4.13")
          val imcCVC5 = imc(300_000, "cvc5:1.0.8")
          val imcMathSAT = imc(300_000, "mathsat:5.6.10")
          val imc = kind(300_000, "Z3")

          expl then predcart then predbool then bmc then kind then imcCVC5 then imcMathSAT then imc

          Pair(expl, imc)
        }
      } else {
        error("Only single-procedure or inlineable programs are supported right now.")
      }

    return STM(startingConfig, edges)
  }

  val inProcessStm = getStm(true)
  val notInProcessStm = getStm(false)

  val inProcess = HierarchicalNode("InProcess", inProcessStm)
  val notInProcess = HierarchicalNode("NotInprocess", notInProcessStm)

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(false)
  else STM(inProcess, setOf(fallbackEdge))
}
