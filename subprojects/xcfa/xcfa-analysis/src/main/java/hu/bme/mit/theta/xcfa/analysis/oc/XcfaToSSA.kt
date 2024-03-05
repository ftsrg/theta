package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager

internal val Expr<*>.vars get() = ExprUtils.getVars(this)

fun XCFA.toSSA(): XCFA {
    val passManager = ProcedurePassManager(listOf(SSAPass()))
    val copy: XcfaProcedureBuilder.() -> XcfaProcedureBuilder = {
        XcfaProcedureBuilder(
            name = name,
            manager = passManager,
            params = getParams().toMutableList(),
            vars = getVars().toMutableSet(),
            locs = getLocs().toMutableSet(),
            edges = getEdges().toMutableSet(),
            metaData = metaData.toMutableMap()
        ).also { it.copyMetaLocs(this) }
    }

    val builder = XcfaBuilder("${name}_SSA", vars.toMutableSet())
    procedureBuilders.forEach { builder.addProcedure(it.copy()) }
    initProcedureBuilders.forEach { (proc, params) ->
        val initProc = builder.getProcedures().find { it.name == proc.name } ?: proc.copy()
        builder.addEntryPoint(initProc, params)
    }
    return builder.build()
}

class SSAPass : ProcedurePass {

    private val ssaUtils = SSAUtils()

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        builder.getEdges().toSet().forEach { edge ->
            builder.removeEdge(edge)
            builder.addEdge(edge.withLabel(ssaUtils.toSSA(edge)))
        }
        return builder
    }
}
