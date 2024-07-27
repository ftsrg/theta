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
package hu.bme.mit.theta.xcfa.analysis

import com.google.common.base.Preconditions
import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.analysis.algorithm.AbstractMonolithicTransFunc
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Exprs.Ite
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import java.util.*
import java.util.List
import java.util.stream.Collectors
import kotlin.collections.HashMap
import kotlin.collections.LinkedHashSet
import kotlin.collections.Map
import kotlin.collections.MutableMap
import kotlin.collections.Set
import kotlin.collections.any
import kotlin.collections.associateBy
import kotlin.collections.associateWith
import kotlin.collections.component1
import kotlin.collections.component2
import kotlin.collections.filter
import kotlin.collections.filterIsInstance
import kotlin.collections.filterNotNull
import kotlin.collections.find
import kotlin.collections.flatMap
import kotlin.collections.fold
import kotlin.collections.isNotEmpty
import kotlin.collections.listOf
import kotlin.collections.map
import kotlin.collections.mapIndexed
import kotlin.collections.mapNotNull
import kotlin.collections.maxOfOrNull
import kotlin.collections.none
import kotlin.collections.plus
import kotlin.collections.set
import kotlin.collections.setOf
import kotlin.collections.toList
import kotlin.collections.toSet
import kotlin.jvm.optionals.getOrNull

class XcfaMonolithicTransFunc(xcfa: XCFA) : AbstractMonolithicTransFunc() {

    lateinit var locMap: Map<XcfaLocation, Int>

    init {
        Preconditions.checkArgument(xcfa.initProcedures.size == 1)
        val proc = checkNotNull(xcfa.initProcedures.stream().findFirst().get().first)
        val labels = proc.edges.stream()
            .flatMap { `$this$getFlatLabels`: XcfaEdge -> `$this$getFlatLabels`.getFlatLabels().stream() }
            .collect(Collectors.toSet())
        Preconditions.checkArgument(
            labels.stream().noneMatch { i: XcfaLabel? -> !(i is StmtLabel || i is NopLabel || i is InvokeLabel) })
        if (labels.stream().anyMatch { i: XcfaLabel? -> i is InvokeLabel }) {
            multiProc(xcfa, proc)
        } else {
            singleProc(proc)
        }
    }

    @OptIn(ExperimentalStdlibApi::class)
    private fun multiProc(xcfa: XCFA, proc: XcfaProcedure) {
        val cG = xcfa.callGraph()
        val longestCallPath = longestPathFrom(proc, cG)
        checkState(longestCallPath != Int.MAX_VALUE, "Cannot handle statically-infinitely-recursive programs.")

        val procedures = LinkedHashSet<XcfaProcedure>()
        val waitList = LinkedList<XcfaProcedure>()
        waitList.add(proc)
        while (waitList.isNotEmpty()) {
            val top = waitList.pop()
            procedures.add(top)
            waitList.addAll(cG[top] ?: setOf())
        }
        procedures as Set<XcfaProcedure>
        val locs = procedures.flatMap { it.locs }.toSet()
        val edges = procedures.flatMap { it.edges }.toSet()

        var i = 0
        locMap = locs.associateWith { i++ }
        val callsiteMap = edges.flatMap { it.getFlatLabels() }.filterIsInstance<InvokeLabel>().associateWith { i++ }

        val stackDepthVar = Decls.Var("__curr_depth_", Int())
        val locVars = (0..longestCallPath).associateWith { Decls.Var("__loc_${it}_", Int()) }
        val callsiteVars = (0..longestCallPath).associateWith { Decls.Var("__proc_${it}_", Int()) }
        val getCurrLoc = (0..longestCallPath).fold(Int(-1) as Expr<IntType>) { acc, idx ->
            Ite(Eq(stackDepthVar.ref, Int(idx)), locVars[idx]!!.ref, acc)
        }
        val getCurrCallsite = (0..longestCallPath).fold(Int(-1) as Expr<IntType>) { acc, idx ->
            Ite(Eq(stackDepthVar.ref, Int(idx)), callsiteVars[idx]!!.ref, acc)
        }

        fun setCurrLoc(iExpr: Expr<IntType>) = NonDetStmt.of(
            (0..longestCallPath).map {
                SequenceStmt.of(
                    listOf(
                        Assume(Eq(stackDepthVar.ref, Int(it))),
                        Assign(locVars[it]!!, iExpr)
                    )
                )
            }
        )

        /**
         *  1. stack++
         *  2. callsite[stack] = invokelabel_id
         *  3. loc[stack] = initloc_id
         */
        fun enterFuncStmt(proc: XcfaProcedure, invokeLabel: InvokeLabel) = SequenceStmt.of(
            listOf(Assign(stackDepthVar, Add(stackDepthVar.ref, Int(1)))) +
                NonDetStmt.of((0..longestCallPath).map {
                    SequenceStmt.of(
                        listOf(
                            Assume(Eq(stackDepthVar.ref, Int(it))),
                            Assign(callsiteVars[it]!!, Int(callsiteMap[invokeLabel]!!))
                        )
                    )
                }) +
                setCurrLoc(Int(locMap[proc.initLoc]!!))                 // new loc in stack
        )

        /**
         *  1. find invokelabel
         *  2. assign exit params
         *  3. stack--
         */
        fun exitFuncStmt(proc: XcfaProcedure) = SequenceStmt.of(
            listOf(
                AssumeStmt.of(Eq(getCurrLoc, Int(locMap[proc.finalLoc.get()]!!))),
                NonDetStmt.of(callsiteMap.map { (invokeLabel, idx) ->
                    SequenceStmt.of(
                        listOf(Assume(Eq(getCurrCallsite, Int(idx)))) +
                            proc.params.mapIndexed { i, (varDecl, dir) ->           // param assignments
                                if (dir != ParamDirection.IN) {
                                    val param = invokeLabel.params[i] as RefExpr<*>
                                    Assign(
                                        cast(param.decl as VarDecl<*>, varDecl.type), cast(varDecl.ref, varDecl.type)
                                    )
                                } else {
                                    null
                                }
                            }.filterNotNull()
                    )
                })
            ) + Assign(stackDepthVar, Sub(stackDepthVar.ref, Int(1)))

        )

        val tranList = edges.map { e: XcfaEdge ->
            val flatLabels = e.getFlatLabels()
            if (flatLabels.size == 1 && flatLabels[0] is InvokeLabel) {
                val invokeLabel = flatLabels[0] as InvokeLabel
                val calledProc = xcfa.procedures.find { it.name == invokeLabel.name } ?: error(
                    "No such procedure ${invokeLabel.name}"
                )
                SequenceStmt.of(
                    listOf(
                        AssumeStmt.of(Eq(getCurrLoc, Int(locMap[e.source]!!))),     // entry loc match
                        setCurrLoc(Int(locMap[e.target]!!))                         // exit loc match
                    ) + calledProc.params.mapIndexed { i, (varDecl, dir) ->               // param assignments
                        if (dir != ParamDirection.OUT) {
                            Assign(cast(varDecl, varDecl.type), cast(invokeLabel.params[i], varDecl.type))
                        } else {
                            null
                        }
                    }.filterNotNull() +
                        enterFuncStmt(calledProc, invokeLabel)                            // stack assignment
                )
            } else {
                checkState(flatLabels.none { it is InvokeLabel }, "InvokeLabels deserve their own private edge.")
                SequenceStmt.of(
                    listOf(
                        AssumeStmt.of(Eq(getCurrLoc, Int(locMap[e.source]!!))),
                        e.label.toStmt(),
                        setCurrLoc(Int(locMap[e.target]!!))
                    )
                )
            }
        }.toList() + procedures.filter { it.finalLoc.isPresent }.map { exitFuncStmt(it) }

        val trans = NonDetStmt.of(tranList)
        val transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0))
        transExpr = SmartBoolExprs.And(transUnfold.exprs)
        initExpr = And(
            listOf(
                Eq(locVars[0]!!.ref, Int(locMap[proc.initLoc]!!)),
                Eq(stackDepthVar.ref, Int(0)),
            )
        )
        firstIndex = VarIndexingFactory.indexing(0)
        offsetIndex = transUnfold.indexing
        propExpr = And(procedures.mapNotNull { it.errorLoc.getOrNull()?.let { Neq(getCurrLoc, Int(locMap[it]!!)) } })
    }

    private fun singleProc(proc: XcfaProcedure) {
        Preconditions.checkArgument(proc.errorLoc.isPresent)
        var i = 0
        val map: MutableMap<XcfaLocation, Int> = HashMap()
        locMap = map
        for (x in proc.locs) {
            map[x] = i++
        }
        val locVar = Decls.Var("__loc_", Int())
        val tranList = proc.edges.map { e: XcfaEdge ->
            SequenceStmt.of(
                List.of(
                    AssumeStmt.of(IntExprs.Eq(locVar.ref, Int(map[e.source]!!))),
                    e.label.toStmt(),
                    AssignStmt.of(locVar, Int(map[e.target]!!))
                )
            )
        }.toList()
        val trans = NonDetStmt.of(tranList)
        val transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0))
        transExpr = SmartBoolExprs.And(transUnfold.exprs)
        initExpr = IntExprs.Eq(locVar.ref, Int(map[proc.initLoc]!!))
        firstIndex = VarIndexingFactory.indexing(0)
        offsetIndex = transUnfold.indexing
        propExpr = IntExprs.Neq(locVar.ref, Int(map[proc.errorLoc.get()]!!))
    }

    fun toMonolithicExpr() = MonolithicExpr(
        initExpr, transExpr, propExpr, offsetIndex
    )

}

private fun XCFA.callGraph(): Map<XcfaProcedure, Set<XcfaProcedure>> =
    procedures.associateBy { it.name }.let { map ->
        procedures.associateWith {
            it.edges.flatMap(XcfaEdge::getFlatLabels).filterIsInstance<InvokeLabel>()
                .mapNotNull { map[it.name] }
                .toSet()
        }
    }

private fun longestPathFrom(proc: XcfaProcedure, cG: Map<XcfaProcedure, Set<XcfaProcedure>>): Int {
    lateinit var helper: (XcfaProcedure, Set<XcfaProcedure>) -> Int
    helper = { current, reachedSet ->
        if (cG[current]?.any { reachedSet.contains(it) } == true) {
            Int.MAX_VALUE
        } else {
            cG[current]?.maxOfOrNull { helper(it, reachedSet + it) }?.plus(1) ?: 0
        }
    }
    return helper(proc, setOf(proc))
}
