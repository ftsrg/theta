/*
 *  Copyright 2022 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators
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
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState.Companion.createLookup
import hu.bme.mit.theta.xcfa.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.changeVars
import java.util.*
import java.util.function.Predicate

open class XcfaAnalysis<S: ExprState, P: Prec> (
        private val corePartialOrd: PartialOrd<XcfaState<S>>,
        private val coreInitFunc: InitFunc<XcfaState<S>, XcfaPrec<P>>,
        private val coreTransFunc: TransFunc<XcfaState<S>, XcfaAction, XcfaPrec<P>>,
) : Analysis<XcfaState<S>, XcfaAction, XcfaPrec<P>> {
    override fun getPartialOrd(): PartialOrd<XcfaState<S>> = corePartialOrd
    override fun getInitFunc(): InitFunc<XcfaState<S>, XcfaPrec<P>> = coreInitFunc
    override fun getTransFunc(): TransFunc<XcfaState<S>, XcfaAction, XcfaPrec<P>> = coreTransFunc
}

/// Common

fun getXcfaLts() = LTS<XcfaState<out ExprState>, XcfaAction> {
            s -> s.processes.map {
                proc -> proc.value.locs.peek().outgoingEdges.map { XcfaAction(proc.key, it.withLabel(it.label.changeVars(proc.value.varLookup.peek()))) }.filter { !s.apply(it).first.bottom }
            }.flatten()
        }

enum class ErrorDetection {
    ERROR_LOCATION,
    DATA_RACE
}

fun getXcfaErrorPredicate(errorDetection: ErrorDetection): Predicate<XcfaState<out ExprState>> = when(errorDetection) {
    ErrorDetection.ERROR_LOCATION ->
        Predicate<XcfaState<out ExprState>>{ s -> s.processes.any { it.value.locs.peek().error }}
    ErrorDetection.DATA_RACE -> {
        val collectGlobalVars: XcfaLabel.(List<VarDecl<*>>) -> Map<VarDecl<*>, Boolean> = { globalVars ->
            collectVarsWithAccessType().filter { labelVar -> globalVars.any { it == labelVar.key } }
        }
        val getGlobalVars = { xcfa: XCFA, edge: XcfaEdge ->
            val globalVars = xcfa.vars.map(XcfaGlobalVar::wrappedVar)
            var label = edge.label
            if (label is SequenceLabel && label.labels.size == 1) label = label.labels[0]
            if (label is FenceLabel && label.labels.contains("ATOMIC_BEGIN")) {
                val vars = mutableMapOf<VarDecl<*>, Boolean>() // true, if write
                val processed = mutableSetOf<XcfaEdge>()
                val unprocessed = mutableListOf(edge)
                while (unprocessed.isNotEmpty()) {
                    val e = unprocessed.removeFirst()
                    val eLabel = e.label
                    if (!(eLabel is FenceLabel && eLabel.labels.contains("ATOMIC_END"))) {
                        eLabel.collectGlobalVars(globalVars).forEach { (varDecl, isWrite) ->
                            vars[varDecl] = isWrite || (vars[varDecl] ?: false)
                        }
                        processed.add(e)
                        unprocessed.addAll(e.target.outgoingEdges subtract processed)
                    }
                }
                vars
            } else {
                label.collectGlobalVars(globalVars)
            }
        }
        Predicate<XcfaState<out ExprState>> { s ->
            val xcfa = s.xcfa!!
            if (s.mutexes.containsKey("")) return@Predicate false
            for (process1 in s.processes)
                for (process2 in s.processes)
                    if (process1.key != process2.key)
                        for (edge1 in process1.value.locs.peek().outgoingEdges)
                            for (edge2 in process2.value.locs.peek().outgoingEdges) {
                                val globalVars1 = getGlobalVars(xcfa, edge1)
                                val globalVars2 = getGlobalVars(xcfa, edge2)
                                val intersection = globalVars1.keys intersect globalVars2.keys
                                if (intersection.any { globalVars1[it] == true || globalVars2[it] == true })
                                    return@Predicate true
                            }
            false
        }
    }
}

fun <S: ExprState> getPartialOrder(partialOrd: PartialOrd<S>) =
        PartialOrd<XcfaState<S>>{s1, s2 -> s1.processes == s2.processes && partialOrd.isLeq(s1.sGlobal, s2.sGlobal)}

private fun <S: XcfaState<out ExprState>, P: XcfaPrec<out Prec>> getXcfaArgBuilder(
        analysis: Analysis<S, XcfaAction, P>,
        ltsSupplier: () -> LTS<XcfaState<out ExprState>, XcfaAction>,
        errorDetection: ErrorDetection)
: ArgBuilder<S, XcfaAction, P> =
        ArgBuilder.create(
                ltsSupplier(),
                analysis,
                getXcfaErrorPredicate(errorDetection)
        )

fun <S: XcfaState<out ExprState>, P: XcfaPrec<out Prec>> getXcfaAbstractor(
        analysis: Analysis<S, XcfaAction, P>,
        argNodeComparator: ArgNodeComparators.ArgNodeComparator,
        stopCriterion: StopCriterion<*, *>,
        logger: Logger,
        ltsSupplier: () -> LTS<XcfaState<out ExprState>, XcfaAction>,
        errorDetection: ErrorDetection
): Abstractor<out XcfaState<out ExprState>, XcfaAction, out XcfaPrec<out Prec>> =
        BasicAbstractor.builder(getXcfaArgBuilder(analysis, ltsSupplier, errorDetection))
                .waitlist(PriorityWaitlist.create(argNodeComparator))
                .stopCriterion(stopCriterion as StopCriterion<S, XcfaAction>).logger(logger).build() // TODO: can we do this nicely?



/// EXPL

private fun getExplXcfaInitFunc(xcfa: XCFA, solver: Solver): (XcfaPrec<ExplPrec>) -> List<XcfaState<ExplState>> {
    val processInitState = xcfa.initProcedures.mapIndexed { i, it ->
        val initLocStack: LinkedList<XcfaLocation> = LinkedList()
        initLocStack.add(it.first.initLoc)
        Pair(i, XcfaProcessState(initLocStack, varLookup = LinkedList(listOf(createLookup(it.first, "", "")))))
    }.toMap()
    return { p -> ExplInitFunc.create(solver, True()).getInitStates(p.p).map { XcfaState(xcfa, processInitState, it) } }
}
private fun getExplXcfaTransFunc(solver: Solver, maxEnum: Int): (XcfaState<ExplState>, XcfaAction, XcfaPrec<ExplPrec>) -> List<XcfaState<ExplState>> {
    val explTransFunc = ExplStmtTransFunc.create(solver, maxEnum)
    return { s, a, p ->
        val (newSt, newAct) = s.apply(a)
        explTransFunc.getSuccStates(newSt.sGlobal, newAct, p.p).map { newSt.withState(it) }
    }
}

class ExplXcfaAnalysis(xcfa: XCFA, solver: Solver, maxEnum: Int) : XcfaAnalysis<ExplState, ExplPrec>(
        corePartialOrd = getPartialOrder { s1, s2 -> s1.isLeq(s2) },
        coreInitFunc = getExplXcfaInitFunc(xcfa, solver),
        coreTransFunc = getExplXcfaTransFunc(solver, maxEnum)
)

/// PRED

private fun getPredXcfaInitFunc(xcfa: XCFA, predAbstractor: PredAbstractor): (XcfaPrec<PredPrec>) -> List<XcfaState<PredState>> {
    val processInitState = xcfa.initProcedures.mapIndexed { i, it ->
        val initLocStack: LinkedList<XcfaLocation> = LinkedList()
        initLocStack.add(it.first.initLoc)
        Pair(i, XcfaProcessState(initLocStack, varLookup = LinkedList(listOf(createLookup(it.first, "", "")))))
    }.toMap()
    return { p -> PredInitFunc.create(predAbstractor, True()).getInitStates(p.p).map { XcfaState(xcfa, processInitState, it) } }
}
private fun getPredXcfaTransFunc(predAbstractor: PredAbstractors.PredAbstractor): (XcfaState<PredState>, XcfaAction, XcfaPrec<PredPrec>) -> List<XcfaState<PredState>> {
    val predTransFunc = PredTransFunc.create<XcfaAction>(predAbstractor)
    return { s, a, p ->
        val (newSt, newAct) = s.apply(a)
        predTransFunc.getSuccStates(newSt.sGlobal, newAct, p.p).map { newSt.withState(it) }
    }
}

class PredXcfaAnalaysis(xcfa: XCFA, solver: Solver, predAbstractor: PredAbstractor) : XcfaAnalysis<PredState, PredPrec>(
        corePartialOrd = getPartialOrder(PredOrd.create(solver)),
        coreInitFunc = getPredXcfaInitFunc(xcfa, predAbstractor),
        coreTransFunc = getPredXcfaTransFunc(predAbstractor)
)
