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
import hu.bme.mit.theta.xcfa.AssignStmtLabel
import hu.bme.mit.theta.xcfa.model.ParamDirection.*
import hu.bme.mit.theta.xcfa.model.global
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import hu.bme.mit.theta.xcfa.passes.UnusedLocRemovalPass
import org.junit.Test

class ThyssenXcfaDslTest {

    fun sendChan(chan: VarDecl<*>, chanAck: VarDecl<*>, syncEdgeContent: List<XcfaLabel>) = SequenceLabel(
        listOf(
            AssignStmtLabel(chan, True(), EmptyMetaData),
            FenceLabel(setOf("ATOMIC_BEGIN")),
            StmtLabel(Stmts.Assume(chanAck.ref as Expr<BoolType>)),
            AssignStmtLabel(chanAck, False(), EmptyMetaData),
            *syncEdgeContent.toTypedArray(),
            FenceLabel(setOf("ATOMIC_END"))
        ),
        EmptyMetaData
    )
    fun receiveChan(chan: VarDecl<*>, chanAck: VarDecl<*>, syncEdgeContent: List<XcfaLabel>): SequenceLabel {
        val labels = listOf(
            FenceLabel(setOf("ATOMIC_BEGIN")),
            StmtLabel(Stmts.Assume(chan.ref as Expr<BoolType>)),
            AssignStmtLabel(chanAck, True(), EmptyMetaData),
            AssignStmtLabel(chan, False(), EmptyMetaData),
            *syncEdgeContent.toTypedArray(),
            FenceLabel(setOf("ATOMIC_END")),
            StmtLabel(Stmts.Assume(Not(chanAck.ref as Expr<BoolType>))),
        )
        return SequenceLabel(
            labels,
            EmptyMetaData
        )
    }

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
        lateinit var runDiagAck: VarDecl<BoolType>
        lateinit var runAAck: VarDecl<BoolType>
        lateinit var runBAck: VarDecl<BoolType>

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
            runDiagAck = bool("runDiagAck", False()) 
            runAAck = bool("runAAck", False()) 
            runBAck = bool("runBAck", False()) 
        }
        threadlocal {
            //y = "y" type Int() init "2"
        }

        val schedulerProc = procedure("GlobalScheduler") {
            (init to "Stable") { nop() }

            ("Stable" to "L1") { sendChan(runDiag, runDiagAck, listOf()) }

            ("L1" to "L2a") { sendChan(runA, runAAck, listOf()) }
            ("L1" to "L2b") { sendChan(runB, runBAck, listOf()) }

            ("L2a" to "L3a") { sendChan(runB, runBAck, listOf()) }
            ("L2b" to "L3b") { sendChan(runA, runAAck, listOf()) }

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
                receiveChan(runDiag, runDiagAck, listOf(
                        havoc(newFailureA),
                        havoc(newFailureB),
                        assume(Not(And(newFailureA.ref, newFailureB.ref))),
                        okA assign And(okA.ref, Not(newFailureA.ref)),
                        okB assign And(okB.ref, Not(newFailureB.ref)),

                        havoc(newTransientCommA),
                        havoc(newTransientCommB),
                        havoc(newPermanentCommA),
                        havoc(newPermanentCommB),
                        assume(commFailureAssumptions),
                        AtoBCommPermFailed assign newPermanentCommA.ref,
                        BtoACommPermFailed assign newPermanentCommB.ref,
                        AtoBCommOk assign And(Not(AtoBCommPermFailed.ref), Not(newTransientCommA.ref)),
                        BtoACommOk assign And(Not(BtoACommPermFailed.ref), Not(newTransientCommB.ref)),

                        okAforB assign Ite<BoolType>(AtoBCommOk.ref, okA.ref, okAforB.ref),
                        okBforA assign Ite<BoolType>(BtoACommOk.ref, okB.ref, okBforA.ref)
                    )
                )
            }
        }
        val RWA_A = procedure("RWA_A") {
            (init to "Master") { nop() }
            ("Master" to "Master") { receiveChan(runA, runAAck, listOf(
                assume("okA and okBforA")
            )) }
            ("Master" to "Standalone") { receiveChan(runA, runAAck, listOf(
                assume("okA and not okBforA")
            )) }
            ("Standalone" to "Standalone") { receiveChan(runA, runAAck, listOf(
                assume("okA")
            )) }
            ("Standalone" to "Error") { receiveChan(runA, runAAck, listOf(
                assume("(not okA)")
            )) }
            ("Error" to "Error") { receiveChan(runA, runAAck, listOf(
                nop()
            )) }
            ("Master" to "Passive") { receiveChan(runA, runAAck, listOf(
                assume("(and (not okA) okBforA)")
            )) }
            ("Master" to "Error") { receiveChan(runA, runAAck, listOf(
                assume("(and (not okA) (not okBforA))")
            )) }
            ("Passive" to "Error") { receiveChan(runA, runAAck, listOf(
                assume("(not okBforA)")
            )) }
            ("Passive" to "Passive") { receiveChan(runA, runAAck, listOf(
                assume("okBforA")
            )) }
        }
        val RWA_B = procedure("RWA_A") {
            (init to "Silent") { nop() }
            ("Silent" to "Silent") { receiveChan(runA, runAAck, listOf(
                assume("(and okB okAforB)")
            )) }
            ("Silent" to "Standalone") { receiveChan(runA, runAAck, listOf(
                assume("(and okB (not okAforB))")
            )) }
            ("Standalone" to "Standalone") { receiveChan(runA, runAAck, listOf(
                assume("okB")
            )) }
            ("Standalone" to "Error") { receiveChan(runA, runAAck, listOf(
                assume("(not okB)")
            )) }
            ("Error" to "Error") { receiveChan(runA, runAAck, listOf(
                nop()
            )) }
            ("Silent" to "Passive") { receiveChan(runA, runAAck, listOf(
                assume("(and (not okB) okAforB)")
            )) }
            ("Silent" to "Error") { receiveChan(runA, runAAck, listOf(
                assume("(and (not okB) (not okAforB))")
            )) }
            ("Passive" to "Error") { receiveChan(runA, runAAck, listOf(
                assume("(not okAforB)")
            )) }
            ("Passive" to "Passive") { receiveChan(runA, runAAck, listOf(
                assume("okAforB")
            )) }
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
    fun defineXcfa() {
        val xcfa = getXcfa()
        println(xcfa.toDot())
    }

}