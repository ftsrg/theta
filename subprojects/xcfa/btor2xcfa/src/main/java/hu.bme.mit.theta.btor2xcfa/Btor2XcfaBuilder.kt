package hu.bme.mit.theta.btor2xcfa

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.NotExpr
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
///////////////////////////////////////////////
        // Initek
        var lastLoc = procBuilder.initLoc
        var newLoc = XcfaLocation("l${i}", false, false, false, EmptyMetaData)
        // initekhez
        procBuilder.addLoc(newLoc)
        Btor2Circuit.states.forEach {
            it.value.getVar()?.let{varDecl ->
                if(varDecl.name.startsWith(("init_"))){
                    val edge = XcfaEdge(lastLoc,newLoc, StmtLabel(AssignStmt.of(it.value.state?.getVar(), it.value.value?.getExpr() as Expr<BvType>)), EmptyMetaData)
                    procBuilder.addEdge(edge)

                    // Amit tudunk 1 élre helyezzük, tehát az első élen vannak az initek
                    //lastLoc=loc
                }
            }
        }
        i++
        lastLoc=newLoc
///////////////////////////////////////////////
        // Havoc változók
        // Miután felvettük az initeket mehetnek a havoc változók
        if(Btor2Circuit.states.filter { it.value.getVar()?.name?.startsWith("input_") == true }.isNotEmpty()){
            newLoc = XcfaLocation("l${i}", false, false, false, EmptyMetaData)
            procBuilder.addLoc(newLoc)
            Btor2Circuit.states.forEach {
                it.value.getVar()?.let{ varDecl ->
                    if(varDecl.name.startsWith(("input_"))){
                        val edge = XcfaEdge(lastLoc, newLoc, StmtLabel(HavocStmt.of(varDecl)), EmptyMetaData)
                        procBuilder.addEdge(edge)
                    }
                }
            }
            i++
            lastLoc=newLoc
        }

/////////////////////////////////////////////
        // Végigmegyünk az operationökön
        // Check: Kigyűjtöm a feldolgozott node idkat akár itt v korábban,,
        // Megfelelő sorrendben kell belerakni
        // Gyors check h feldolgozotak között van e és hibával elszállunk ha nem
        // az operandusainak a nid-jeire kell a check
        Btor2Circuit.ops.forEach() {
            val loc = XcfaLocation("l${i}", false, false, false, EmptyMetaData)

            procBuilder.addLoc(loc)

            val edge = XcfaEdge(lastLoc, loc, StmtLabel(it.value.getStmt(false)), EmptyMetaData)
            procBuilder.addEdge(edge)
            i++
            lastLoc=loc
        }
        procBuilder.createErrorLoc()
        // Errorkezelése
        // Egyzserű pédáink vannak tehát egyelőre csak bad van benne
        val bad = Btor2Circuit.properties.values.first()

        procBuilder.addEdge(XcfaEdge(lastLoc, procBuilder.errorLoc.get(), StmtLabel(AssumeStmt.of(bad.getExpr())),EmptyMetaData))
        newLoc = XcfaLocation("l${i}", false, false, false, EmptyMetaData)
        procBuilder.addEdge(XcfaEdge(lastLoc, newLoc, StmtLabel(AssumeStmt.of(Not(bad.getExpr()))),EmptyMetaData))

        //Circuit folytatása
        // ha nincsen next akkor azt el kelll havocolni
        Btor2Circuit.states.forEach {
            it.value.getVar()?.let{varDecl ->
                if(varDecl.name.startsWith(("next_"))){
                    val firstLoc = procBuilder.getLocs().elementAt(1)
                    procBuilder.addEdge(XcfaEdge(newLoc, firstLoc, StmtLabel(AssignStmt.of(it.value.state?.getVar(), it.value.getExpr() as Expr<BvType>)),EmptyMetaData))

                }
            }
        }
        return xcfaBuilder.build()
    }
}

class Btor2Pass() : ProcedurePassManager() {
    // No optimization for now c:
}