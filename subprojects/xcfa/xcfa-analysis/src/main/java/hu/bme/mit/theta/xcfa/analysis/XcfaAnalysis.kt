/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.analysis.algorithm.arg.ArgBuilder
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.bounded.BoundedLtsChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterion
import hu.bme.mit.theta.analysis.expl.ExplInitFunc
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ExplStmtTransFunc
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.pred.*
import hu.bme.mit.theta.analysis.pred.PredAbstractors.PredAbstractor
import hu.bme.mit.theta.analysis.prod2.Prod2InitFunc
import hu.bme.mit.theta.analysis.prod2.Prod2Ord
import hu.bme.mit.theta.analysis.prod2.Prod2Prec
import hu.bme.mit.theta.analysis.prod2.Prod2State
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredAbstractors
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredDedicatedTransFunc
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredStmtTransFunc
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.ptr.getPtrInitFunc
import hu.bme.mit.theta.analysis.ptr.getPtrPartialOrd
import hu.bme.mit.theta.analysis.ptr.getPtrTransFunc
import hu.bme.mit.theta.analysis.unit.*
import hu.bme.mit.theta.analysis.waitlist.Waitlist
import hu.bme.mit.theta.analysis.zone.ZoneOrd
import hu.bme.mit.theta.analysis.zone.ZonePrec
import hu.bme.mit.theta.analysis.zone.ZoneState
import hu.bme.mit.theta.common.Try
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.clock.op.ClockOps.Reset
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.utils.TypeUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState.Companion.createLookup
import hu.bme.mit.theta.xcfa.analysis.coi.XcfaCoi
import hu.bme.mit.theta.xcfa.analysis.timed.DataClockXcfaActionPartition
import hu.bme.mit.theta.xcfa.analysis.timed.XcfaZoneInitFunc
import hu.bme.mit.theta.xcfa.analysis.timed.XcfaZoneTransFunc
import hu.bme.mit.theta.xcfa.analysis.timed.addVarsAndClocks
import hu.bme.mit.theta.xcfa.analysis.timed.getActiveClocks
import hu.bme.mit.theta.xcfa.analysis.timed.getInvariants
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.changeVars
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.util.*

open class XcfaAnalysis<S : ExprState, P : Prec>(
  private val corePartialOrd: PartialOrd<XcfaState<PtrState<S>>>,
  private val coreInitFunc: InitFunc<XcfaState<PtrState<S>>, XcfaPrec<P>>,
  private var coreTransFunc: TransFunc<XcfaState<PtrState<S>>, XcfaAction, XcfaPrec<P>>,
  coneOfInfluence: XcfaCoi? = null,
) : Analysis<XcfaState<PtrState<S>>, XcfaAction, XcfaPrec<P>> {

  init {
    if (coneOfInfluence != null) {
      coneOfInfluence.coreTransFunc =
        transFunc
          as TransFunc<XcfaState<out PtrState<out ExprState>>, XcfaAction, XcfaPrec<out Prec>>
      coreTransFunc =
        coneOfInfluence.transFunc as TransFunc<XcfaState<PtrState<S>>, XcfaAction, XcfaPrec<P>>
    }
  }

  override fun getPartialOrd(): PartialOrd<XcfaState<PtrState<S>>> = corePartialOrd

  override fun getInitFunc(): InitFunc<XcfaState<PtrState<S>>, XcfaPrec<P>> = coreInitFunc

  override fun getTransFunc(): TransFunc<XcfaState<PtrState<S>>, XcfaAction, XcfaPrec<P>> =
    coreTransFunc
}

private val tmpVarCache = mutableMapOf<Pair<VarDecl<*>, Int>, VarDecl<*>>()

private fun getTmpVar(originalVar: VarDecl<*>, tmpCnt: Int) =
  tmpVarCache.getOrPut(originalVar to tmpCnt) {
    Var("tmp${tmpCnt}_" + originalVar.name, originalVar.type)
  }

fun getCoreXcfaLts() =
  LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction> { s ->
    s.processes
      .map { proc ->
        if (proc.value.locs.peek().final) {
          listOf(
            XcfaAction(
              proc.key,
              XcfaEdge(
                proc.value.locs.peek(),
                proc.value.locs.peek(),
                SequenceLabel(
                  listOf(
                    proc.value.paramStmts.peek().second,
                    ReturnLabel(proc.value.returnStmts.peek()),
                  )
                ),
                proc.value.locs.peek().metadata,
              ),
              nextCnt = s.sGlobal.nextCnt,
            )
          )
        } else if (!proc.value.paramsInitialized) {
          val threadLocalClocks = s.xcfa?.let { xcfa ->
              xcfa.clocks.filter { it.threadLocal }.map { it.wrappedVar }
          } ?: emptyList()
          val procClocks = proc.value.procedure?.clocks ?: emptyList()
          val lookup = proc.value.foldVarLookup()
          val newClockResetLabels = SequenceLabel(
              (threadLocalClocks + procClocks)
                  .map { ClockOpLabel(Reset(cast(lookup[it], Rat()), 0)) }
          )
          val invariantLabels = SequenceLabel(getInvariants(s.processes
              .map { Pair(
                  it.value.locs.peek(),
                  it.value.foldVarLookup()
              )}.toMap()
          ))
          listOf(
            XcfaAction(
              proc.key,
              XcfaEdge(
                proc.value.locs.peek(),
                proc.value.locs.peek(),
                SequenceLabel(listOf(
                    proc.value.paramStmts.peek().first,
                    newClockResetLabels,
                    ClockDelayLabel(getActiveClocks(s)),
                    invariantLabels,
                )),
                proc.value.locs.peek().metadata,
              ),
              nextCnt = s.sGlobal.nextCnt,
            )
          )
        } else {
          var invokeParameterCount = proc.value.invokeParameterCounter
          proc.value.locs.peek().outgoingEdges.map { edge ->
            val newLabel = SequenceLabel(edge.label.changeVars(proc.value.varLookup.peek())
              .getFlatLabels().map { label ->
                when (label) {
                  is InvokeLabel -> {
                    val procedure =
                      s.xcfa?.procedures?.find { proc -> proc.name == label.name }
                        ?: error("No such method ${label.name}.")
                    val lookup: MutableMap<VarDecl<*>, VarDecl<*>> = LinkedHashMap()
                    SequenceLabel(
                      listOf(
                        procedure.params
                          .withIndex()
                          .filter { it.value.second != ParamDirection.OUT }
                          .map { iVal ->
                            val originalVar = iVal.value.first
                            val tempVar = getTmpVar(originalVar, invokeParameterCount++)
                            lookup[originalVar] = tempVar
                            StmtLabel(
                              Stmts.Assign(
                                TypeUtils.cast(tempVar, tempVar.type),
                                TypeUtils.cast(label.params[iVal.index], tempVar.type),
                              ),
                              metadata = label.metadata,
                            )
                          },
                        listOf(label.copy(tempLookup = lookup)),
                      )
                        .flatten()
                    )
                  }
                  is StartLabel -> {
                    val procedure =
                      s.xcfa?.procedures?.find { proc -> proc.name == label.name }
                        ?: error("No such method ${label.name}.")
                    val lookup: MutableMap<VarDecl<*>, VarDecl<*>> = LinkedHashMap()
                    SequenceLabel(
                      listOf(
                        procedure.params
                          .withIndex()
                          .filter { it.value.second != ParamDirection.OUT }
                          .mapNotNull { iVal ->
                            val originalVar = iVal.value.first
                            val tempVar = getTmpVar(originalVar, invokeParameterCount++)
                            lookup[originalVar] = tempVar
                            val trial =
                              Try.attempt {
                                StmtLabel(
                                  Stmts.Assign(
                                    TypeUtils.cast(tempVar, tempVar.type),
                                    TypeUtils.cast(label.params[iVal.index], tempVar.type),
                                  ),
                                  metadata = label.metadata,
                                )
                              }
                            if (trial.isSuccess) {
                              trial.asSuccess().value
                            } else {
                              null
                            }
                          },
                        listOf(label.copy(tempLookup = lookup)),
                      )
                        .flatten()
                    )
                  }
                  is ClockDelayLabel -> {
                    if (s.processes.any { !it.value.paramsInitialized }) {
                      StmtLabel(Assume(False()))
                    } else {
                        val invariants = getInvariants(s.processes
                          .map { (pid, processState) -> Pair(
                              if (pid == proc.key) edge.target else processState.locs.peek(),
                              processState.foldVarLookup()
                          )}.toMap()
                      )
                      SequenceLabel(
                        listOf(
                            ClockDelayLabel(getActiveClocks(s)),
                            SequenceLabel(invariants)
                        ),
                        label.metadata
                      )
                    }
                  }
                  else -> label
                }
              }
            )
            XcfaAction(proc.key, edge.withLabel(newLabel), nextCnt = s.sGlobal.nextCnt)
          }
        }
      }
      .flatten()
      .toSet()
  }

fun getXcfaLts(): LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction> {
  val lts = getCoreXcfaLts()
  return LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction> { s ->
    lts.getEnabledActionsFor(s).filter { !s.apply(it).first.bottom }.toSet()
  }
}

fun <S : ExprState> getPartialOrder(partialOrd: PartialOrd<PtrState<S>>) =
  PartialOrd<XcfaState<PtrState<S>>> { s1, s2 ->
    s1.processes == s2.processes &&
      s1.bottom == s2.bottom &&
      s1.mutexes == s2.mutexes &&
      partialOrd.isLeq(s1.sGlobal, s2.sGlobal)
  }

private fun <S : ExprState> stackIsLeq(s1: XcfaState<PtrState<S>>, s2: XcfaState<PtrState<S>>) =
  s2.processes.keys.all { pid ->
    s1.processes[pid]?.let { ps1 ->
      val ps2 = s2.processes.getValue(pid)
      ps1.locs.peek() == ps2.locs.peek() && ps1.paramsInitialized && ps2.paramsInitialized
    } ?: false
  }

fun <S : ExprState> getStackPartialOrder(partialOrd: PartialOrd<PtrState<S>>) =
  PartialOrd<XcfaState<PtrState<S>>> { s1, s2 ->
    s1.processes.keys == s2.processes.keys &&
      stackIsLeq(s1, s2) &&
      s1.bottom == s2.bottom &&
      s1.mutexes == s2.mutexes &&
      partialOrd.isLeq(s1.withGeneralizedVars(), s2.withGeneralizedVars())
  }

private fun <S : XcfaState<out PtrState<out ExprState>>, P : XcfaPrec<out Prec>> getXcfaArgBuilder(
  analysis: Analysis<S, XcfaAction, P>,
  lts: LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction>,
  errorDetector: XcfaErrorDetector,
): ArgBuilder<S, XcfaAction, P> = ArgBuilder.create(lts, analysis, errorDetector)

fun <S : XcfaState<out PtrState<out ExprState>>, P : XcfaPrec<out Prec>> getXcfaAbstractor(
  analysis: Analysis<S, XcfaAction, P>,
  waitlist: Waitlist<*>,
  stopCriterion: StopCriterion<*, *>,
  logger: Logger,
  lts: LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction>,
  errorDetector: XcfaErrorDetector,
): ArgAbstractor<out XcfaState<out PtrState<out ExprState>>, XcfaAction, out XcfaPrec<out Prec>> =
  XcfaArgAbstractor.builder(getXcfaArgBuilder(analysis, lts, errorDetector))
    .waitlist(waitlist as Waitlist<ArgNode<S, XcfaAction>>) // TODO: can we do this nicely?
    .stopCriterion(stopCriterion as StopCriterion<S, XcfaAction>)
    .logger(logger)
    .projection {
      if (it.xcfa!!.isInlined) it.processes else it.processes.map { (_, p) -> p.locs.peek() }
    }
    .build() // TODO: can we do this nicely?

private fun <S : ExprState, P : Prec> getXcfaInitFunc(
    xcfa : XCFA,
    initFunc : InitFunc<S, P>
) : (XcfaPrec<PtrPrec<P>>) -> List<XcfaState<PtrState<S>>> {
    val processInitState =
        xcfa.initProcedures
            .mapIndexed { i, it ->
                val initLocStack: LinkedList<XcfaLocation> = LinkedList()
                initLocStack.add(it.first.initLoc)
                Pair(
                    i,
                    XcfaProcessState(
                        initLocStack,
                        prefix = "T$i",
                        varLookup = LinkedList(listOf(it.first.createLookup("T$i", includeThreadLocals = true))),
                        procedure = it.first,
                    ),
                )
            }
            .toMap()
    return { p ->
        initFunc.getPtrInitFunc().getInitStates(p.p).map {
            XcfaState(xcfa, processInitState, it)
        }
    }
}

private fun <S : ExprState, P : Prec> getXcfaTransFunc(
    transFunc : TransFunc<S, ExprAction, P>,
    newPrec : (XcfaState<PtrState<S>>, XcfaAction, XcfaPrec<PtrPrec<P>>) -> PtrPrec<P>,
    isHavoc : Boolean,
) : (XcfaState<PtrState<S>>, XcfaAction, XcfaPrec<PtrPrec<P>>) -> List<XcfaState<PtrState<S>>> {
    val ptrTransFunc = transFunc.getPtrTransFunc(isHavoc)
    return { s, a, p ->
        val (newSt, newAct) = s.apply(a)
        ptrTransFunc
            .getSuccStates(newSt.sGlobal, newAct, newPrec(s, a, p))
            .map { newSt.withState(it) }
    }
}

private fun <S : ExprState, P : Prec> getProd2DataZoneTransFunc(
    dataTransFunc : TransFunc<S, ExprAction, P>,
    zoneTransFunc : TransFunc<ZoneState, ExprAction, ZonePrec>,
) = TransFunc<Prod2State<S, ZoneState>, ExprAction, Prod2Prec<P, ZonePrec>> { state, action, prec ->
    val (dataAction, clockAction) = DataClockXcfaActionPartition.getPartition(action as XcfaAction)
    Prod2State.cartesianOrBottom(
        dataTransFunc.getSuccStates(state.state1, dataAction, prec.prec1),
        zoneTransFunc.getSuccStates(state.state2, clockAction, prec.prec2)
    )
}

private fun getLookups(
    xcfaState : XcfaState<*>,
    xcfaAction: XcfaAction
) = listOf(
    xcfaState.processes.map { it.value.varLookup }.flatten(),
    listOf(getTempLookup(xcfaAction.label))
).flatten()

private fun getFoldedLookups(
    xcfaState : XcfaState<*>,
    xcfaAction: XcfaAction
) = xcfaState.processes.map { it.value.foldVarLookup() + getTempLookup(xcfaAction.label) }

/// EXPL

private fun getExplInitFunc(
    solver: Solver,
) = ExplInitFunc.create(solver, True())

private fun getExplTransFunc(
    solver: Solver,
    maxEnum: Int,
) = (ExplStmtTransFunc.create(solver, maxEnum) as TransFunc<ExplState, ExprAction, ExplPrec>)

class ExplXcfaAnalysis(
  xcfa: XCFA,
  solver: Solver,
  maxEnum: Int,
  partialOrd: PartialOrd<XcfaState<PtrState<ExplState>>>,
  isHavoc: Boolean,
  coi: XcfaCoi? = null,
) :
  XcfaAnalysis<ExplState, PtrPrec<ExplPrec>>(
    corePartialOrd = partialOrd,
    coreInitFunc = getXcfaInitFunc(xcfa, getExplInitFunc(solver)),
    coreTransFunc = getXcfaTransFunc(
        getExplTransFunc(solver, maxEnum),
        { s, a, p -> p.p.addVars(getLookups(s, a)) },
        isHavoc,
    ),
    coneOfInfluence = coi,
  )

class ExplZoneXcfaAnalysis(
    xcfa: XCFA,
    solver: Solver,
    maxEnum: Int,
    partialOrd: PartialOrd<ExplState>,
    isHavoc: Boolean,
    coi: XcfaCoi? = null,
) : XcfaAnalysis<Prod2State<ExplState, ZoneState>, PtrPrec<Prod2Prec<ExplPrec, ZonePrec>>>(
    corePartialOrd = getPartialOrder(
        Prod2Ord.create(
            partialOrd, ZoneOrd.getInstance()
        ).getPtrPartialOrd()
    ),
    coreInitFunc = getXcfaInitFunc(
        xcfa,
        Prod2InitFunc.create(
            getExplInitFunc(solver),
            XcfaZoneInitFunc(xcfa.initProcedures.map { it.first.initLoc })
        ),
    ),
    coreTransFunc = getXcfaTransFunc(
        getProd2DataZoneTransFunc(
            getExplTransFunc(solver, maxEnum),
            XcfaZoneTransFunc() as TransFunc<ZoneState, ExprAction, ZonePrec>
        ),
        { s, a, p -> p.p.addVarsAndClocks(s, getLookups(s, a)) },
        isHavoc,
    ),
    coneOfInfluence = coi,
)

/// PRED

private fun getPredInitFunc(
    predAbstractor: PredAbstractor,
) = PredInitFunc.create(predAbstractor, True())

private fun getPredTransFunc(
    predAbstractor: PredAbstractors.PredAbstractor,
) = (PredTransFunc.create<StmtAction>(predAbstractor) as TransFunc<PredState, ExprAction, PredPrec>)

class PredXcfaAnalysis(
  xcfa: XCFA,
  solver: Solver,
  predAbstractor: PredAbstractor,
  partialOrd: PartialOrd<XcfaState<PtrState<PredState>>>,
  isHavoc: Boolean,
  coi: XcfaCoi? = null,
) :
  XcfaAnalysis<PredState, PtrPrec<PredPrec>>(
    corePartialOrd = partialOrd,
    coreInitFunc = getXcfaInitFunc(xcfa, getPredInitFunc(predAbstractor)),
    coreTransFunc = getXcfaTransFunc(
        getPredTransFunc(predAbstractor),
        { s, a, p -> p.p.addVars(getFoldedLookups(s, a)) },
        isHavoc,
    ),
    coneOfInfluence = coi,
  )

class PredZoneXcfaAnalysis(
    xcfa: XCFA,
    predAbstractor: PredAbstractor,
    partialOrd: PartialOrd<PredState>,
    isHavoc: Boolean,
    coi: XcfaCoi? = null,
) : XcfaAnalysis<Prod2State<PredState, ZoneState>, PtrPrec<Prod2Prec<PredPrec, ZonePrec>>>(
    corePartialOrd = getPartialOrder(
        Prod2Ord.create(
            partialOrd, ZoneOrd.getInstance()
        ).getPtrPartialOrd()
    ),
    coreInitFunc = getXcfaInitFunc(
        xcfa,
        Prod2InitFunc.create(
            getPredInitFunc(predAbstractor),
            XcfaZoneInitFunc(xcfa.initProcedures.map { it.first.initLoc })
        ),
    ),
    coreTransFunc = getXcfaTransFunc(
        getProd2DataZoneTransFunc(
            getPredTransFunc(predAbstractor),
            XcfaZoneTransFunc() as TransFunc<ZoneState, ExprAction, ZonePrec>
        ),
        { s, a, p -> p.p.addVarsAndClocks(s, getFoldedLookups(s, a)) },
        isHavoc,
    ),
    coneOfInfluence = coi,
)

/// EXPL_PRED_COMBINED

private fun getExplPredInitFunc(
  solver: Solver,
) = Prod2InitFunc.create(
  ExplInitFunc.create(solver, True()),
  PredInitFunc.create(PredAbstractors.cartesianAbstractor(solver), True()),
)

private fun getExplPredStmtTransFunc(
  solver: Solver,
) = Prod2ExplPredStmtTransFunc.create<StmtAction>(solver)
  as TransFunc<Prod2State<ExplState, PredState>, ExprAction, Prod2Prec<ExplPrec, PredPrec>>

private fun getExplPredSplitTransFunc(
  solver: Solver,
) = Prod2ExplPredDedicatedTransFunc.create<StmtAction>(Prod2ExplPredAbstractors.booleanAbstractor(solver))
  as TransFunc<Prod2State<ExplState, PredState>, ExprAction, Prod2Prec<ExplPrec, PredPrec>>

class ExplPredCombinedXcfaAnalysis(
  xcfa: XCFA,
  solver: Solver,
  explPredSplit: Boolean,
  partialOrd: PartialOrd<XcfaState<PtrState<Prod2State<ExplState, PredState>>>>,
  isHavoc: Boolean,
  coi: XcfaCoi? = null,
) :
  XcfaAnalysis<Prod2State<ExplState, PredState>, PtrPrec<Prod2Prec<ExplPrec, PredPrec>>>(
    corePartialOrd = partialOrd,
    coreInitFunc = getXcfaInitFunc(xcfa, getExplPredInitFunc(solver)),
    coreTransFunc = getXcfaTransFunc(
      if (explPredSplit) getExplPredSplitTransFunc(solver) else getExplPredStmtTransFunc(solver),
      { s, a, p -> p.p.addVars(getFoldedLookups(s, a)) },
      isHavoc
    ),
    coneOfInfluence = coi,
  )

/// UNIT

private fun getUnitXcfaPartialOrd(xcfa: XCFA): PartialOrd<XcfaState<PtrState<UnitState>>> {
  val ptrPartialOrd = UnitAnalysis.getInstance().partialOrd.getPtrPartialOrd()
  return if (xcfa.isInlined) {
    getPartialOrder(ptrPartialOrd)
  } else {
    getStackPartialOrder(ptrPartialOrd)
  }
}

private fun getUnitInitFunc() = InitFunc<UnitState, UnitPrec> { _ -> listOf(UnitState.getInstance()) }

private fun getUnitTransFunc() = TransFunc<UnitState, ExprAction, UnitPrec> { s, _, _ -> listOf(s) }

class UnitXcfaAnalysis(
  xcfa: XCFA,
  isHavoc: Boolean,
  coi: XcfaCoi? = null,
): XcfaAnalysis<UnitState, PtrPrec<UnitPrec>>(
    corePartialOrd = getUnitXcfaPartialOrd(xcfa),
    coreInitFunc = getXcfaInitFunc(xcfa, getUnitInitFunc()),
    coreTransFunc = getXcfaTransFunc(
        getUnitTransFunc(),
        {_, _, _ -> PtrPrec(UnitPrec.getInstance())},
        isHavoc,
    ),
    coneOfInfluence = coi,
  )

fun getBoundedXcfaChecker(
  xcfa: XCFA,
  errorDetection: ErrorDetection,
  bound: Int,
  solver: Solver,
  isHavoc: Boolean = false,
  coi: XcfaCoi? = null,
): BoundedLtsChecker<XcfaState<PtrState<UnitState>>, XcfaAction, XcfaPrec<PtrPrec<UnitPrec>>> {
  val lts = getXcfaLts()
  return getBoundedXcfaChecker(xcfa, lts, errorDetection, bound, solver, isHavoc, coi)
}

fun getBoundedXcfaChecker(
  xcfa: XCFA,
  lts: LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction>,
  errorDetection: ErrorDetection,
  bound: Int,
  solver: Solver,
  isHavoc: Boolean = false,
  coi: XcfaCoi? = null,
): BoundedLtsChecker<XcfaState<PtrState<UnitState>>, XcfaAction, XcfaPrec<PtrPrec<UnitPrec>>> {
  val analysis = UnitXcfaAnalysis(xcfa, isHavoc, coi)
  val target = getXcfaErrorDetector(errorDetection)
  val prec = XcfaPrec(PtrPrec(UnitPrec.getInstance()))
  return BoundedLtsChecker(lts, analysis, target, bound, prec, solver)
}
