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
package hu.bme.mit.theta.xcfa.cli

import hu.bme.mit.theta.analysis.algorithm.arg.ArgBuilder
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy.FULL
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType.efficient
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.AssignStmtLabel
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAnalysis
import hu.bme.mit.theta.xcfa.analysis.getCoreXcfaLts
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.params.Backend.CEGAR
import hu.bme.mit.theta.xcfa.cli.params.CexMonitorOptions.CHECK
import hu.bme.mit.theta.xcfa.cli.params.CexMonitorOptions.DISABLE
import hu.bme.mit.theta.xcfa.cli.params.ConeOfInfluenceMode.NO_COI
import hu.bme.mit.theta.xcfa.cli.params.Domain.EXPL
import hu.bme.mit.theta.xcfa.cli.params.ExprSplitterOptions.WHOLE
import hu.bme.mit.theta.xcfa.cli.params.InitPrec.ALLVARS
import hu.bme.mit.theta.xcfa.cli.params.InitPrec.EMPTY
import hu.bme.mit.theta.xcfa.cli.params.POR.NOPOR
import hu.bme.mit.theta.xcfa.cli.params.Refinement.SEQ_ITP
import hu.bme.mit.theta.xcfa.cli.params.Search.DFS
import hu.bme.mit.theta.xcfa.cli.params.Search.ERR
import hu.bme.mit.theta.xcfa.model.ParamDirection.*
import hu.bme.mit.theta.xcfa.model.global
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.*
import org.junit.Test
import java.io.File

class ThyssenXcfaDslTest {

    private fun getXcfa() = xcfa("example") {
        val transientCommFailureEnabled = true
        val permanentCommFailureEnabled = true

        lateinit var okA: VarDecl<BoolType>
        lateinit var okB: VarDecl<BoolType>
        lateinit var okAforB: VarDecl<BoolType>
        lateinit var okBforA: VarDecl<BoolType>
        lateinit var AtoBCommOk: VarDecl<BoolType>
        lateinit var BtoACommOk: VarDecl<BoolType>
        lateinit var AtoBCommPermFailed: VarDecl<BoolType>
        lateinit var BtoACommPermFailed: VarDecl<BoolType>

        // Chans
        lateinit var runDiag: VarDecl<BoolType>
        lateinit var runA: VarDecl<BoolType>
        lateinit var runB: VarDecl<BoolType>

        global {
            okA = bool("okA", True())
            okB = bool("okB", True())
            okAforB = bool("okAforB", True()) 
            okBforA = bool("okBforA", True()) 
            AtoBCommOk = bool("AtoBCommOk", True()) 
            BtoACommOk = bool("BtoACommOk", True()) 
            AtoBCommPermFailed = bool("AtoBCommPermFailed", False()) 
            BtoACommPermFailed = bool("BtoACommPermFailed", False()) 
            runDiag = bool("runDiag", False()) 
            runA = bool("runA", False()) 
            runB = bool("runB", False())
        }
        threadlocal {
            //y = "y" type Int() init "2"
        }

        val schedulerProc = procedure("GlobalScheduler") {
            (init to "Stable") { nop() }

            ("Stable" to "L1") { syncSend(runDiag) }

            ("L1" to "L2a") { syncSend(runA) }
            ("L1" to "L2b") { syncSend(runB) }

            ("L2a" to "L3a") { syncSend(runB) }
            ("L2b" to "L3b") { syncSend(runA) }

            ("L3a" to "Stable") { nop() }
            ("L3b" to "Stable") { nop() }
            ("Stable" to err) { assume(False()) }
        }
        val diagnosticsProc = procedure("Diagnostics") {
            val newFailureA = bool("newFailureA") 
            val newFailureB = bool("newFailureB") 
            val newTransientCommA = bool("newTransientCommA") 
            val newTransientCommB = bool("newTransientCommB") 
            val newPermanentCommA = bool("newPermanentCommA") 
            val newPermanentCommB = bool("newPermanentCommB") 

            (init to "L0") {nop()}

            val commFailureAssumptions =
                "(and (=> (or newTransientCommA newTransientCommB) ${transientCommFailureEnabled}) " +
                    "(=> (or newPermanentCommA newPermanentCommB) ${permanentCommFailureEnabled}) " +
                    "(or (not newPermanentCommA) (not newPermanentCommB)))"

            ("L0" to "L0") {
                syncRecv(runDiag)
                havoc(newFailureA)
                havoc(newFailureB)
                assume(Not(And(newFailureA.ref, newFailureB.ref)))
                okA assign And(okA.ref, Not(newFailureA.ref))
                okB assign And(okB.ref, Not(newFailureB.ref))

                havoc(newTransientCommA)
                havoc(newTransientCommB)
                havoc(newPermanentCommA)
                havoc(newPermanentCommB)
                assume(commFailureAssumptions)
                AtoBCommPermFailed assign newPermanentCommA.ref
                BtoACommPermFailed assign newPermanentCommB.ref
                AtoBCommOk assign And(Not(AtoBCommPermFailed.ref), Not(newTransientCommA.ref))
                BtoACommOk assign And(Not(BtoACommPermFailed.ref), Not(newTransientCommB.ref))

                okAforB assign Ite<BoolType>(AtoBCommOk.ref, okA.ref, okAforB.ref)
                okBforA assign Ite<BoolType>(BtoACommOk.ref, okB.ref, okBforA.ref)
            }
        }
        val RWA_A = procedure("RWA_A") {
            (init to "Master") { nop() }
            ("Master" to "Master") {
                syncRecv(runA)
                assume(okA and okBforA)
            }
            ("Master" to "Standalone") {
                syncRecv(runA)
                assume(okA and !okBforA)
            }
            ("Standalone" to "Standalone") {
                syncRecv(runA)
                assume("okA")
            }
            ("Standalone" to "Error") {
                syncRecv(runA)
                assume(!okA)
            }
            ("Error" to "Error") {
                syncRecv(runA)
                nop()
            }
            ("Master" to "Passive") {
                syncRecv(runA)
                assume(!okA and okBforA)
            }
            ("Master" to "Error") {
                syncRecv(runA)
                assume(!okA and !okBforA)
            }
            ("Passive" to "Error") {
                syncRecv(runA)
                assume(!okBforA)
            }
            ("Passive" to "Passive") {
                syncRecv(runA)
                assume(okBforA)
            }
        }
        val RWA_B = procedure("RWA_B") {
            (init to "Silent") { nop() }
            ("Silent" to "Silent") {
                syncRecv(runB)
                assume(okB and okAforB)
            }
            ("Silent" to "Standalone") {
                syncRecv(runB)
                //assume(okB and !okAforB)
            }
            ("Standalone" to "Standalone") {
                syncRecv(runB)
                assume(okB)
            }
            ("Standalone" to "Error") {
                syncRecv(runB)
                assume(!okB)
            }
            ("Error" to "Error") {
                syncRecv(runB)
                nop()
            }
            ("Silent" to "Passive") {
                syncRecv(runB)
                assume(!okB and okAforB)
            }
            ("Silent" to "Error") {
                syncRecv(runB)
                assume(!okB and !okAforB)
            }
            ("Passive" to "Error") {
                syncRecv(runB)
                assume(!okAforB)
            }
            ("Passive" to "Passive") {
                syncRecv(runB)
                assume(okAforB)
            }
        }

        val main = procedure("main") {
            val scheduler = "scheduler" type Int()
            val diagnostics = "diagnostics" type Int()
            val rwaA = "rwaA" type Int()
            val rwaB = "rwaB" type Int()
            (init to "L0") {
                scheduler.start(schedulerProc)
                diagnostics.start(diagnosticsProc)
                rwaA.start(RWA_A)
                rwaB.start(RWA_B)
            }
            ("L0" to final) {
                scheduler.join()
                diagnostics.join()
                rwaA.join()
                rwaB.join()
            }
        }

        main.start()
    }

    @Test
    fun checkXcfa() {
        LbePass.level = LbePass.LbeLevel.LBE_LOCAL
        val origXcfa = getXcfa()
        println(origXcfa.toDot())

        val inputConfig = InputConfig(
            xcfaWCtx = Triple(origXcfa, listOf(), ParseContext()),
            property = ErrorDetection.CustomError {
                it.processes.values.any { it.locs.peek().name == "GlobalScheduler_Stable" } &&
                it.processes.values.any { it.locs.peek().name == "RWA_B_Standalone" }
                     && it.processes.values.any { it.locs.peek().name in setOf("RWA_A_Master", "RWA_A_Standalone") }
            }
        )
        val frontendConfig = FrontendConfig(
            lbeLevel = LbePass.level,
            loopUnroll = LoopUnrollPass.UNROLL_LIMIT,
            inputType = InputType.C,
            specConfig = CFrontendConfig(arithmetic = efficient),
        )
        val backendConfig = BackendConfig(
            backend = CEGAR,
            timeoutMs = 0,
            specConfig =
            CegarConfig(
                initPrec = ALLVARS,
                porLevel = NOPOR,
                porRandomSeed = -1,
                coi = NO_COI,
                cexMonitor = DISABLE,
                abstractorConfig =
                CegarAbstractorConfig(
                    abstractionSolver = "Z3",
                    validateAbstractionSolver = false,
                    domain = EXPL,
                    maxEnum = 0,
                    search = DFS,
                ),
                refinerConfig = CegarRefinerConfig(
                    refinementSolver = "Z3",
                    validateRefinementSolver = false,
                    refinement = SEQ_ITP,
                    exprSplitter = WHOLE,
                    pruneStrategy = FULL,
                ),
            ),
        )
        val outputConfig = OutputConfig(
            enableOutput = true,
            resultFolder = File("F:\\egyetem\\thesta\\theta\\subprojects\\xcfa\\xcfa\\src\\test\\temp")
        )
        val result = runConfig(
            XcfaConfig(
                inputConfig,
                frontendConfig,
                backendConfig,
                outputConfig,
                DebugConfig()
            ),
            ConsoleLogger(Logger.Level.SUBSTEP),
            ConsoleLogger(Logger.Level.SUBSTEP),
            true
        )
    }

    @Test
    fun tracegen() {
        LbePass.level = LbePass.LbeLevel.LBE_LOCAL
        val origXcfa = getXcfa()
        val inputConfig =
            InputConfig(
                xcfaWCtx = Triple(origXcfa, listOf(), ParseContext()),
                property = ErrorDetection.NO_ERROR,
            )
        val frontendConfig =
            FrontendConfig(
                lbeLevel = LbePass.level,
                loopUnroll = LoopUnrollPass.UNROLL_LIMIT,
                inputType = InputType.C,
                specConfig = CFrontendConfig(arithmetic = efficient),
            )
        val backendConfig =
            BackendConfig(
                backend = Backend.TRACEGEN,
                timeoutMs = 0,
                specConfig =
                TracegenConfig(
                    abstractorConfig =
                    CegarAbstractorConfig(
                        abstractionSolver = "Z3",
                        validateAbstractionSolver = false,
                        domain = EXPL,
                        maxEnum = 1,
                        search = DFS,
                    )
                ),
            )
        val outputConfig =
            OutputConfig(
                enableOutput = true,
                resultFolder = File("F:\\egyetem\\thesta\\theta\\subprojects\\xcfa\\xcfa\\src\\test\\temp"),
            )
        runConfig(
            XcfaConfig(inputConfig, frontendConfig, backendConfig, outputConfig, DebugConfig()),
            ConsoleLogger(Logger.Level.SUBSTEP),
            ConsoleLogger(Logger.Level.SUBSTEP),
            true,
        )
    }
}