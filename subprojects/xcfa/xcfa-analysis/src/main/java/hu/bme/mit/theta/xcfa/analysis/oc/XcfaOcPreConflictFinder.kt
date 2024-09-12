package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.*
import hu.bme.mit.theta.core.decl.VarDecl

@Suppress("unused")
enum class ManualConflictFinderConfig {

    NONE, RF, RF_WS_FR
}

internal fun findManualConflicts(
    threads: Set<Thread>,
    events: Map<VarDecl<*>, Map<Int, List<XcfaEvent>>>,
    rfs: Map<VarDecl<*>, Set<Relation<XcfaEvent>>>,
    config: ManualConflictFinderConfig
): List<Reason> {
    if (config == ManualConflictFinderConfig.NONE) return emptyList()
    val exactPo = XcfaExactPo(threads)
    val po = { from: E, to: E -> exactPo.isPo(from, to) }
    val flatRfs = rfs.values.flatten().toMutableList()
    val conflicts = mutableListOf<Reason>()

    fun findSimplePath(from: E, to: E): Reason? {
        if (po(from, to)) return PoReason
        return flatRfs.find { po(from, it.from) && po(it.to, to) }?.let { RelationReason(it) }
    }

    // Cycle of two RF edges (plus po edges)
    for (i in 0 until flatRfs.size) {
        for (j in i + 1 until flatRfs.size) {
            val rf1 = flatRfs[i]
            val rf2 = flatRfs[j]
            if (po(rf1.to, rf2.from) && po(rf2.to, rf1.from)) {
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
                findSimplePath(w, rf.to)?.let { wBeforeRf ->
                    findSimplePath(rf.from, w)?.let {
                        conflicts.add(WriteSerializationReason(rf, w, wBeforeRf) and it)
                    }
                }
                // FR
                findSimplePath(rf.from, w)?.let { wAfterRf ->
                    findSimplePath(w, rf.to)?.let {
                        conflicts.add(FromReadReason(rf, w, wAfterRf) and it)
                    }
                }
            }
        }
    }

    return conflicts
}
