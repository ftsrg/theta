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
package hu.bme.mit.theta.xcfa.analysis;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Neq
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.StmtLabel;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import java.util.*

fun XCFA.toMonolithicExpr(): MonolithicExpr {
    Preconditions.checkArgument(this.initProcedures.size == 1)
    val proc = this.initProcedures.stream().findFirst().orElse(null).first
    Preconditions.checkArgument(proc.edges.map { it.getFlatLabels() }.flatten().none { it !is StmtLabel })
    Preconditions.checkArgument(proc.errorLoc.isPresent)

    val map = mutableMapOf<XcfaLocation, Int>()
    for ((i, x) in proc.locs.withIndex()) {
        map[x] = i;
    }
    val locVar = Decls.Var("__loc_", IntExprs.Int())
    val tranList = proc.edges.map { (source, target, label): XcfaEdge ->
        SequenceStmt.of(listOf(
            AssumeStmt.of(Eq(locVar.ref, IntExprs.Int(map[source]!!))),
            label.toStmt(),
            AssignStmt.of(locVar,
                IntExprs.Int(map[target]!!))
        ))
    }.toList()
    val trans = NonDetStmt.of(tranList)
    val transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0))

    return MonolithicExpr(
        initExpr = Eq(locVar.ref, IntExprs.Int(map[proc.initLoc]!!)),
        transExpr = And(transUnfold.exprs),
        propExpr = Neq(locVar.ref, IntExprs.Int(map[proc.errorLoc.get()]!!)),
        transOffsetIndex = transUnfold.indexing
    )
}

fun XCFA.valToAction(val1: Valuation, val2: Valuation): XcfaAction {
    val val1Map = val1.toMap()
    val val2Map = val2.toMap()
    var i = 0
    val map: MutableMap<XcfaLocation, Int> = HashMap()
    for (x in this.procedures.first { it.name == "main" }.locs) {
        map[x] = i++
    }
    return XcfaAction(
        pid = 0,
        edge = this.procedures.first { it.name == "main" }.edges.first { edge ->
            map[edge.source] == (val1Map[val1Map.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt() &&
                map[edge.target] == (val2Map[val2Map.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt()
        })
}

fun XCFA.valToState(val1: Valuation): XcfaState<PtrState<ExplState>> {
    val valMap = val1.toMap()
    var i = 0
    val map: MutableMap<Int, XcfaLocation> = HashMap()
    for (x in this.procedures.first { it.name == "main" }.locs) {
        map[i++] = x
    }
    return XcfaState(
        xcfa = this,
        processes = mapOf(Pair(0, XcfaProcessState(
            locs = LinkedList(
                listOf(map[(valMap[valMap.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt()])),
            varLookup = LinkedList(),
        ))),
        PtrState(ExplState.of(
            ImmutableValuation.from(
                val1.toMap()
                    .filter { it.key.name != "__loc_" && !it.key.name.startsWith("__temp_") }
                    .map { Pair(Decls.Var("_" + "_" + it.key.name, it.key.type), it.value) }.toMap()))),
        mutexes = emptyMap(),
        threadLookup = emptyMap(),
        bottom = false
    )
}
