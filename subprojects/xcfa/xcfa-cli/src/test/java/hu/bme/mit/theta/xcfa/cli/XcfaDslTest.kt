package hu.bme.mit.theta.xcfa.cli

import hu.bme.mit.theta.analysis.utils.ArgVisualizer
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.visualization.Graph
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.z3.Z3SolverManager
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.model.ParamDirection.*
import org.junit.Assert
import org.junit.Test
import java.io.File

class XcfaDslTest {

    private fun getSyncXcfa() = xcfa("example") {
        val proc1 = procedure("proc1") {
            val a = "a" type Int() direction IN
            val b = "b" type Int() direction OUT

            (init to final) {
                b assign a.ref
            }
        }
        val main = procedure("main") {
            val tmp = "tmp" type Int()
            (init to "L1") {
                proc1("1", tmp.ref)
            }
            ("L1" to final) {
                assume("(= tmp 1)")
            }
            ("L1" to err) {
                assume("(/= tmp 1)")
            }
        }

        main.start()
    }

    private fun getAsyncXcfa() = xcfa("example") {
        val proc1 = procedure("proc1") {
            val a = "a" type Int() direction IN
            val b = "b" type Int() direction OUT

            (init to final) {
                b assign a.ref
            }
        }
        val main = procedure("main") {
            val tmp = "tmp" type Int()
            val thr1 = "thr1" type Int()
            (init to "L1") {
                thr1.start(proc1, "1", tmp.ref)
            }
            ("L1" to final) {
                thr1.join()
                assume("(= tmp 1)")
            }
            ("L1" to err) {
                thr1.join()
                assume("(/= tmp 1)")
            }
        }

        main.start()
    }

    @Test
    fun verifyXcfa() {
        SolverManager.registerSolverManager(Z3SolverManager.create())
        val config = XcfaCegarConfig(maxEnum = 1, search = Search.BFS, initPrec = InitPrec.ALLVARS)

        val xcfa = getAsyncXcfa()
        val xcfaDotFile = File("/tmp/output", "xcfa.dot")
        xcfaDotFile.writeText(xcfa.toDot())

        val safetyResult = config.check(xcfa, ConsoleLogger(Logger.Level.DETAIL))
        val argFile = File("/tmp/output", "arg-${safetyResult.isSafe}.dot")
        val g: Graph = ArgVisualizer.getDefault().visualize(safetyResult.arg)
        argFile.writeText(GraphvizWriter.getInstance().writeString(g))
        Assert.assertTrue(safetyResult.isSafe)
    }

}