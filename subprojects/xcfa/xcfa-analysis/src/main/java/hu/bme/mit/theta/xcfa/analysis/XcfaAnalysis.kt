/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.*
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder
import hu.bme.mit.theta.analysis.algorithm.ArgNode
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterion
import hu.bme.mit.theta.analysis.expl.ExplInitFunc
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ExplStmtTransFunc
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.pred.*
import hu.bme.mit.theta.analysis.pred.PredAbstractors.PredAbstractor
import hu.bme.mit.theta.analysis.waitlist.Waitlist
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.utils.TypeUtils
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState.Companion.createLookup
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.getGlobalVars
import hu.bme.mit.theta.xcfa.isWritten
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.changeVars
import hu.bme.mit.theta.xcfa.startsAtomic
import java.util.*
import java.util.function.Predicate

open class XcfaAnalysis<S : ExprState, P : Prec>(
    private val corePartialOrd: PartialOrd<XcfaState<S>>,
    private val coreInitFunc: InitFunc<XcfaState<S>, XcfaPrec<P>>,
    private val coreTransFunc: TransFunc<XcfaState<S>, XcfaAction, XcfaPrec<P>>,
) : Analysis<XcfaState<S>, XcfaAction, XcfaPrec<P>> {

    override fun getPartialOrd(): PartialOrd<XcfaState<S>> = corePartialOrd
    override fun getInitFunc(): InitFunc<XcfaState<S>, XcfaPrec<P>> = coreInitFunc
    override fun getTransFunc(): TransFunc<XcfaState<S>, XcfaAction, XcfaPrec<P>> = coreTransFunc
}

/// Common
private var tempCnt: Int = 0
fun getCoreXcfaLts() = LTS<XcfaState<out ExprState>, XcfaAction> { s ->
    s.processes.map { proc ->
        if (proc.value.locs.peek().final) {
            listOf(XcfaAction(proc.key,
                XcfaEdge(proc.value.locs.peek(), proc.value.locs.peek(), SequenceLabel(listOf(
                    proc.value.paramStmts.peek().second,
                    ReturnLabel(proc.value.returnStmts.peek()),
                )))))
        } else if (!proc.value.paramsInitialized) {
            listOf(XcfaAction(proc.key, XcfaEdge(proc.value.locs.peek(), proc.value.locs.peek(),
                proc.value.paramStmts.peek().first)))
        } else {
            proc.value.locs.peek().outgoingEdges.map { edge ->
                val newLabel = edge.label.changeVars(proc.value.varLookup.peek())
                val flatLabels = newLabel.getFlatLabels()
                if (flatLabels.any { it is InvokeLabel || it is StartLabel }) {
                    val newNewLabel = SequenceLabel(flatLabels.map { label ->
                        if (label is InvokeLabel) {
                            val procedure = s.xcfa?.procedures?.find { proc -> proc.name == label.name }
                                ?: error("No such method ${label.name}.")
                            val lookup: MutableMap<VarDecl<*>, VarDecl<*>> = LinkedHashMap()
                            SequenceLabel(listOf(procedure.params.withIndex()
                                .filter { it.value.second != ParamDirection.OUT }.map { iVal ->
                                    val originalVar = iVal.value.first
                                    val tempVar = Var("tmp${tempCnt++}_" + originalVar.name,
                                        originalVar.type)
                                    lookup[originalVar] = tempVar
                                    StmtLabel(
                                        Stmts.Assign(
                                            TypeUtils.cast(tempVar, tempVar.type),
                                            TypeUtils.cast(label.params[iVal.index], tempVar.type)),
                                        metadata = label.metadata)
                                }, listOf(label.copy(tempLookup = lookup))).flatten())
                        } else if (label is StartLabel) {
                            val procedure = s.xcfa?.procedures?.find { proc -> proc.name == label.name }
                                ?: error("No such method ${label.name}.")
                            val lookup: MutableMap<VarDecl<*>, VarDecl<*>> = LinkedHashMap()
                            SequenceLabel(listOf(procedure.params.withIndex()
                                .filter { it.value.second != ParamDirection.OUT }.map { iVal ->
                                    val originalVar = iVal.value.first
                                    val tempVar = Var("tmp${tempCnt++}_" + originalVar.name,
                                        originalVar.type)
                                    lookup[originalVar] = tempVar
                                    StmtLabel(
                                        Stmts.Assign(
                                            TypeUtils.cast(tempVar, tempVar.type),
                                            TypeUtils.cast(label.params[iVal.index], tempVar.type)),
                                        metadata = label.metadata)
                                }, listOf(label.copy(tempLookup = lookup))).flatten())
                        } else label
                    })
                    XcfaAction(proc.key, edge.withLabel(newNewLabel))
                } else
                    XcfaAction(proc.key, edge.withLabel(newLabel))
            }
        }
    }.flatten().toSet()
}

fun getXcfaLts(): LTS<XcfaState<out ExprState>, XcfaAction> {
    val lts = getCoreXcfaLts()
    return LTS<XcfaState<out ExprState>, XcfaAction> { s ->
        lts.getEnabledActionsFor(s).filter { !s.apply(it).first.bottom }.toSet()
    }
}

enum class ErrorDetection {
    ERROR_LOCATION,
    DATA_RACE,
    OVERFLOW,
    NO_ERROR
}

fun getXcfaErrorPredicate(
    errorDetection: ErrorDetection): Predicate<XcfaState<out ExprState>> = when (errorDetection) {
    ErrorDetection.ERROR_LOCATION ->
        Predicate<XcfaState<out ExprState>> { s -> s.processes.any { it.value.locs.peek().error } }

    ErrorDetection.DATA_RACE -> {
        Predicate<XcfaState<out ExprState>> { s ->
            val xcfa = s.xcfa!!
            if (s.mutexes.containsKey("")) return@Predicate false
            for (process1 in s.processes)
                for (process2 in s.processes)
                    if (process1.key != process2.key)
                        for (edge1 in process1.value.locs.peek().outgoingEdges)
                            for (edge2 in process2.value.locs.peek().outgoingEdges) {
                                val globalVars1 = edge1.getGlobalVars(xcfa)
                                val globalVars2 = edge2.getGlobalVars(xcfa)
                                val isAtomic1 = edge1.startsAtomic()
                                val isAtomic2 = edge2.startsAtomic()
                                if (!isAtomic1 || !isAtomic2) {
                                    val intersection = globalVars1.keys intersect globalVars2.keys
                                    if (intersection.any { globalVars1[it].isWritten || globalVars2[it].isWritten })
                                        return@Predicate true
                                }
                            }
            false
        }
    }

    ErrorDetection.NO_ERROR, ErrorDetection.OVERFLOW -> Predicate<XcfaState<out ExprState>> { false }
}

fun <S : ExprState> getPartialOrder(partialOrd: PartialOrd<S>) =
    PartialOrd<XcfaState<S>> { s1, s2 ->
        s1.processes == s2.processes && s1.bottom == s2.bottom && s1.mutexes == s2.mutexes && partialOrd.isLeq(
            s1.sGlobal, s2.sGlobal)
    }

private fun <S : XcfaState<out ExprState>, P : XcfaPrec<out Prec>> getXcfaArgBuilder(
    analysis: Analysis<S, XcfaAction, P>,
    lts: LTS<XcfaState<out ExprState>, XcfaAction>,
    errorDetection: ErrorDetection)
    : ArgBuilder<S, XcfaAction, P> =
    ArgBuilder.create(
        lts,
        analysis,
        getXcfaErrorPredicate(errorDetection)
    )

fun <S : XcfaState<out ExprState>, P : XcfaPrec<out Prec>> getXcfaAbstractor(
    analysis: Analysis<S, XcfaAction, P>,
    waitlist: Waitlist<*>,
    stopCriterion: StopCriterion<*, *>,
    logger: Logger,
    lts: LTS<XcfaState<out ExprState>, XcfaAction>,
    errorDetection: ErrorDetection
): Abstractor<out XcfaState<out ExprState>, XcfaAction, out XcfaPrec<out Prec>> =
    BasicAbstractor.builder(getXcfaArgBuilder(analysis, lts, errorDetection))
        .waitlist(waitlist as Waitlist<ArgNode<S, XcfaAction>>) // TODO: can we do this nicely?
        .stopCriterion(stopCriterion as StopCriterion<S, XcfaAction>).logger(logger)
        .projection { it.processes }
        .build() // TODO: can we do this nicely?

/// EXPL

private fun getExplXcfaInitFunc(xcfa: XCFA,
    solver: Solver): (XcfaPrec<ExplPrec>) -> List<XcfaState<ExplState>> {
    val processInitState = xcfa.initProcedures.mapIndexed { i, it ->
        val initLocStack: LinkedList<XcfaLocation> = LinkedList()
        initLocStack.add(it.first.initLoc)
        Pair(i, XcfaProcessState(initLocStack, prefix = "T$i",
            varLookup = LinkedList(listOf(createLookup(it.first, "T$i", "")))))
    }.toMap()
    return { p ->
        ExplInitFunc.create(solver, True()).getInitStates(p.p)
            .map { XcfaState(xcfa, processInitState, it) }
    }
}

private fun getExplXcfaTransFunc(solver: Solver,
    maxEnum: Int): (XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>) -> List<XcfaState<ExplState>> {
    val explTransFunc = ExplStmtTransFunc.create(solver, maxEnum)
    return { s, a, p ->
        val (newSt, newAct) = s.apply(a)
        explTransFunc.getSuccStates(newSt.sGlobal, newAct, p.p.addVars(
            listOf(s.processes.map { it.value.varLookup }.flatten(),
                listOf(getTempLookup(a.label))).flatten())).map { newSt.withState(it) }
    }
}

class ExplXcfaAnalysis(xcfa: XCFA, solver: Solver, maxEnum: Int,
    partialOrd: PartialOrd<XcfaState<ExplState>>) : XcfaAnalysis<ExplState, ExplPrec>(
    corePartialOrd = partialOrd,
    coreInitFunc = getExplXcfaInitFunc(xcfa, solver),
    coreTransFunc = getExplXcfaTransFunc(solver, maxEnum)
)

/// PRED

private fun getPredXcfaInitFunc(xcfa: XCFA,
    predAbstractor: PredAbstractor): (XcfaPrec<PredPrec>) -> List<XcfaState<PredState>> {
    val processInitState = xcfa.initProcedures.mapIndexed { i, it ->
        val initLocStack: LinkedList<XcfaLocation> = LinkedList()
        initLocStack.add(it.first.initLoc)
        Pair(i, XcfaProcessState(initLocStack, prefix = "T$i",
            varLookup = LinkedList(listOf(createLookup(it.first, "T$i", "")))))
    }.toMap()
    return { p ->
        PredInitFunc.create(predAbstractor, True()).getInitStates(p.p)
            .map { XcfaState(xcfa, processInitState, it) }
    }
}

private fun getPredXcfaTransFunc(
    predAbstractor: PredAbstractors.PredAbstractor): (XcfaState<PredState>, XcfaAction, XcfaPrec<PredPrec>) -> List<XcfaState<PredState>> {
    val predTransFunc = PredTransFunc.create<XcfaAction>(predAbstractor)
    return { s, a, p ->
        val (newSt, newAct) = s.apply(a)
        predTransFunc.getSuccStates(newSt.sGlobal, newAct, p.p.addVars(
            listOf(s.processes.map { it.value.varLookup }.flatten(),
                listOf(getTempLookup(a.label))).flatten())).map { newSt.withState(it) }
    }
}

class PredXcfaAnalysis(xcfa: XCFA, solver: Solver, predAbstractor: PredAbstractor,
    partialOrd: PartialOrd<XcfaState<PredState>>) : XcfaAnalysis<PredState, PredPrec>(
    corePartialOrd = partialOrd,
    coreInitFunc = getPredXcfaInitFunc(xcfa, predAbstractor),
    coreTransFunc = getPredXcfaTransFunc(predAbstractor)
)
