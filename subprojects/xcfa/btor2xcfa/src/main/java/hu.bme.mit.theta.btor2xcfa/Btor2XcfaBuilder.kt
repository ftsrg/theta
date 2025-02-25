package hu.bme.mit.theta.btor2xcfa

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.frontend.models.Btor2Circuit
import hu.bme.mit.theta.frontend.models.Btor2Operation
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager

object Btor2XcfaBuilder{
    fun btor2xcfa(circuit: Btor2Circuit) : XCFA {
        var i : Int = 1
        val xcfaBuilder = XcfaBuilder("Btor2XCFA")
        val procBuilder = XcfaProcedureBuilder("main", Btor2Pass())
        xcfaBuilder.addProcedure(procBuilder)
        procBuilder.createInitLoc()

        Btor2Circuit.nodes.forEach() {
            it.value.getVar()?.let { varDecl ->
                procBuilder.addVar(varDecl)
            }
        }

        var lastLoc = procBuilder.initLoc

        Btor2Circuit.inits.forEach() {
            val loc = XcfaLocation("l${i}", false, false, false, EmptyMetaData)

            procBuilder.addLoc(loc)

            val edge = XcfaEdge(lastLoc,loc, StmtLabel(AssignStmt.of(it.value.state.getVar(), it.value.value.getExpr() as Expr<BvType>)), EmptyMetaData)
            procBuilder.addEdge(edge)
            i++
            lastLoc=loc
        }

        Btor2Circuit.ops.forEach() {
            val loc = XcfaLocation("l${i}", false, false, false, EmptyMetaData)

            procBuilder.addLoc(loc)

            val edge = XcfaEdge(lastLoc,loc, StmtLabel(it.value.getStmt(false)), EmptyMetaData)
            procBuilder.addEdge(edge)
            i++
            lastLoc=loc
        }

        procBuilder.createErrorLoc()
        // Errorkezelése
        val bad = Btor2Circuit.bads.values.first()
        val op = bad.operand as Btor2Operation
        // We will cast for now ¯\_(ツ)_/¯

        procBuilder.addEdge(XcfaEdge(lastLoc, procBuilder.errorLoc.get(), StmtLabel(op.getStmt(false)),EmptyMetaData))
        val newLoc = XcfaLocation("l${i}", false, false, false, EmptyMetaData)
        procBuilder.addEdge(XcfaEdge(lastLoc, newLoc, StmtLabel(op.getStmt(true)),EmptyMetaData))

        //Circuit folytatása
        val next = Btor2Circuit.nexts.values.first()
        val firstLoc = procBuilder.getLocs().elementAt(1)
        procBuilder.addEdge(XcfaEdge(newLoc, firstLoc, StmtLabel(AssignStmt.of(next.state.getVar(), next.value.getExpr() as Expr<BvType>)),EmptyMetaData))
        return xcfaBuilder.build()
    }

}

class Btor2Pass() : ProcedurePassManager() {
    // No optimization for now c:
}