package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.*
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not

@Suppress("unused")
enum class ManualConflictFinderConfig {

    NONE, RF, RF_WS_FR
}

internal fun findManualConflicts(
    events: Map<VarDecl<*>, Map<Int, List<XcfaEvent>>>,
    pos: List<Relation<XcfaEvent>>,
    rfs: Map<VarDecl<*>, Set<Relation<XcfaEvent>>>,
    config: ManualConflictFinderConfig
): List<Reason> {
    if (config == ManualConflictFinderConfig.NONE) return emptyList()
    val po = close(pos)
    val flatRfs = rfs.values.flatten().toMutableList()
    val conflicts = mutableListOf<Reason>()

    fun findSimplePath(from: Int, to: Int): Reason? {
        if (po[from][to]) return PoReason
        return flatRfs.find { po[from][it.from.clkId] && po[it.to.clkId][to] }?.let { RelationReason(it) }
    }

    // Cycle of two RF edges (plus po edges)
    for (i in 0 until flatRfs.size) {
        for (j in i + 1 until flatRfs.size) {
            val rf1 = flatRfs[i]
            val rf2 = flatRfs[j]
            if (po[rf1.to.clkId][rf2.from.clkId] && po[rf2.to.clkId][rf1.from.clkId]) {
                conflicts.add(RelationReason(rf1) and RelationReason(rf2))
            }
        }
    }

    if (config == ManualConflictFinderConfig.RF) return conflicts

    // Find WS and FR conflicts
    rfs.forEach { (v, vRfs) ->
        val writes = events[v]?.flatMap { it.value }?.filter { it.type == EventType.WRITE } ?: listOf()
        vRfs.forEach { rf ->
            writes.filter { rf.from != it }.forEach { w ->
                // WS
                findSimplePath(w.clkId, rf.to.clkId)?.let { wBeforeRf ->
                    findSimplePath(rf.from.clkId, w.clkId)?.let {
                        conflicts.add(WriteSerializationReason(rf, w, wBeforeRf) and it)
                    }
                }
                // FR
                findSimplePath(rf.from.clkId, w.clkId)?.let { wAfterRf ->
                    findSimplePath(w.clkId, rf.to.clkId)?.let {
                        conflicts.add(FromReadReason(rf, w, wAfterRf) and it)
                    }
                }
            }
        }
    }

    return conflicts
}

private fun close(pos: List<Relation<XcfaEvent>>): Array<Array<Boolean>> {
    val array = Array(XcfaEvent.cnt) { i -> Array(XcfaEvent.cnt) { j -> i == j } }
    val waitlist = pos.map { it.from.clkId to it.to.clkId }.filter { it.first != it.second }.toMutableList()
    while (waitlist.isNotEmpty()) {
        val (f, t) = waitlist.removeAt(0)
        check(f != t) { "Self-loop is not allowed in program order." }
        if (array[f][t]) continue
        array[f][t] = true
        for (i in array.indices) {
            if (array[i][f] && !array[i][t]) waitlist.add(i to t)
            if (array[t][i] && !array[f][i]) waitlist.add(f to i)
        }
    }
    return array
}
