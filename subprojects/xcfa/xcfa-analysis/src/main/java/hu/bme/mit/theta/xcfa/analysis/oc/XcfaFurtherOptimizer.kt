package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager

internal fun XCFA.optimizeFurther(passes: List<ProcedurePass>): XCFA {
    if (passes.isEmpty()) return this
    val passManager = ProcedurePassManager(passes)
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

    val builder = XcfaBuilder(name, vars.toMutableSet())
    procedureBuilders.forEach { builder.addProcedure(it.copy()) }
    initProcedureBuilders.forEach { (proc, params) ->
        val initProc = builder.getProcedures().find { it.name == proc.name } ?: proc.copy()
        builder.addEntryPoint(initProc, params)
    }
    return builder.build()
}