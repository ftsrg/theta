/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.cli.checkers

import hu.bme.mit.theta.analysis.Analysis
import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgCegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgRefiner
import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyAbstractor
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyAnalysis
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStrategy
import hu.bme.mit.theta.analysis.algorithm.lazy.Prod2LazyStrategy
import hu.bme.mit.theta.analysis.algorithm.lazy.SameAbstractionLazyStrategy
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.BasicConcretizer
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.BwItpStrategy
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.FwItpStrategy
import hu.bme.mit.theta.analysis.algorithm.lazy.lu.LuZoneStrategy
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.AasporRefiner
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.analysis.expr.refinement.MultiExprTraceRefiner
import hu.bme.mit.theta.analysis.expr.refinement.NodePruner
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner
import hu.bme.mit.theta.analysis.expr.refinement.Refutation
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis
import hu.bme.mit.theta.analysis.prod2.Prod2Ord
import hu.bme.mit.theta.analysis.prod2.Prod2Prec
import hu.bme.mit.theta.analysis.prod2.Prod2State
import hu.bme.mit.theta.analysis.ptr.ItpRefToPtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.ptr.getPtrPartialOrd
import hu.bme.mit.theta.analysis.runtimemonitor.CexMonitor
import hu.bme.mit.theta.analysis.runtimemonitor.MonitorCheckpoint
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.analysis.waitlist.Waitlist
import hu.bme.mit.theta.analysis.zone.ZoneInterpolator
import hu.bme.mit.theta.analysis.zone.ZoneLattice
import hu.bme.mit.theta.analysis.zone.ZoneOrd
import hu.bme.mit.theta.analysis.zone.ZonePrec
import hu.bme.mit.theta.analysis.zone.ZoneState
import hu.bme.mit.theta.analysis.zone.lu.LuZoneOrd
import hu.bme.mit.theta.analysis.zone.lu.LuZoneState
import hu.bme.mit.theta.common.Tuple4
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.utils.Lens
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaAnalysis
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaPrecRefiner
import hu.bme.mit.theta.xcfa.analysis.XcfaSingleExprTraceRefiner
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.lazy.createAbstrClockLens
import hu.bme.mit.theta.xcfa.analysis.lazy.createConcrDataLens
import hu.bme.mit.theta.xcfa.analysis.lazy.createConcrProd2Lens
import hu.bme.mit.theta.xcfa.analysis.lazy.createLazyClockLens
import hu.bme.mit.theta.xcfa.analysis.getXcfaPartialOrder
import hu.bme.mit.theta.xcfa.analysis.getStackXcfaPartialOrder
import hu.bme.mit.theta.xcfa.analysis.getXcfaErrorDetector
import hu.bme.mit.theta.xcfa.analysis.getXcfaInitFunc
import hu.bme.mit.theta.xcfa.analysis.getXcfaTransFunc
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.analysis.lazy.XcfaInitAbstractor
import hu.bme.mit.theta.xcfa.analysis.lazy.createConcrLens
import hu.bme.mit.theta.xcfa.analysis.por.AtomicNodePruner
import hu.bme.mit.theta.xcfa.analysis.por.XcfaDporLts
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.analysis.timed.DataClockXcfaActionSplitter
import hu.bme.mit.theta.xcfa.analysis.timed.DataClockXcfaActionSplitter.getClockAction
import hu.bme.mit.theta.xcfa.analysis.timed.DataClockXcfaActionSplitter.getClockActionTransFunc
import hu.bme.mit.theta.xcfa.analysis.timed.DataClockXcfaActionSplitter.getClockActionInvTransFunc
import hu.bme.mit.theta.xcfa.analysis.timed.ItpRefToProd2DataZonePrec
import hu.bme.mit.theta.xcfa.analysis.timed.XcfaLuZonePre
import hu.bme.mit.theta.xcfa.analysis.timed.XcfaZoneAnalysis
import hu.bme.mit.theta.xcfa.analysis.timed.XcfaZoneInvTransFunc
import hu.bme.mit.theta.xcfa.analysis.timed.XcfaZoneTransFunc
import hu.bme.mit.theta.xcfa.analysis.timed.addVarsAndClocks
import hu.bme.mit.theta.xcfa.analysis.timed.getActiveClocks
import hu.bme.mit.theta.xcfa.cli.params.CexMonitorOptions
import hu.bme.mit.theta.xcfa.cli.params.CombinedLazyCegarConfig
import hu.bme.mit.theta.xcfa.cli.params.LazyRefinement
import hu.bme.mit.theta.xcfa.cli.params.POR
import hu.bme.mit.theta.xcfa.cli.params.Refinement
import hu.bme.mit.theta.xcfa.cli.params.TimeDomain
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA

private typealias S = ExprState
private typealias ProdS = Prod2State<out S, out S>
private typealias PtrS = PtrState<ProdS>
private typealias XcfaS = XcfaState<PtrS>
private typealias LazyS = LazyState<XcfaS, XcfaS>

private typealias ProdP = Prod2Prec<Prec, Prec>
private typealias PtrP = PtrPrec<ProdP>
private typealias XcfaP = XcfaPrec<PtrP>

fun getCombinedLazyCegarChecker(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {
  if (config.inputConfig.property.verifiedProperty == ErrorDetection.TERMINATION)
    error("Termination cannot be checked, use LIVENESS_CEGAR as a backend.")

  val combinedConfig = config.backendConfig.specConfig as CombinedLazyCegarConfig

  val cegarConfig = combinedConfig.cegarConfig
  val cegarDomain = cegarConfig.abstractorConfig.domain

  val lazyDomain = combinedConfig.lazyDomain

  val abstractionSolverFactory: SolverFactory =
    getSolver(
      cegarConfig.abstractorConfig.abstractionSolver,
      cegarConfig.abstractorConfig.validateAbstractionSolver,
    )
  val refinementSolverFactory: SolverFactory =
    getSolver(
      cegarConfig.refinerConfig.refinementSolver,
      cegarConfig.refinerConfig.validateRefinementSolver,
    )

  val ignoredVarRegistry = mutableMapOf<VarDecl<*>, MutableSet<S>>()

  val (coi, lts) = cegarConfig.coi.getLts(xcfa, parseContext, cegarConfig.por, ignoredVarRegistry)
  val waitlist =
    if (cegarConfig.por.isDynamic) {
      (cegarConfig.coi.porLts as XcfaDporLts).waitlist
    } else {
      PriorityWaitlist.create<ArgNode<out S, XcfaAction>>(
        cegarConfig.abstractorConfig.search.getComp(xcfa)
      )
    }

  val abstractionSolver = abstractionSolverFactory.createSolver()
  val dataStatePartialOrd = cegarDomain.partialOrd(abstractionSolver) as PartialOrd<S>
  val clockStatePartialOrd = when (lazyDomain.abstrDomain) {
    TimeDomain.ZONE -> ZoneOrd.getInstance()
    TimeDomain.LU -> LuZoneOrd.getInstance()
  }
  val globalStatePartialOrd: PartialOrd<PtrS> =
    Prod2Ord.create(dataStatePartialOrd, clockStatePartialOrd)
      .getPtrPartialOrd()
      as PartialOrd<PtrS>

  val corePartialOrd: PartialOrd<XcfaS> =
    if (xcfa.isInlined) getXcfaPartialOrder(globalStatePartialOrd)
    else getStackXcfaPartialOrder(globalStatePartialOrd)

  ///

  val dataStrategy = SameAbstractionLazyStrategy<S, LazyS, XcfaAction>(
    createConcrDataLens<S>() as Lens<LazyS, S>,
    dataStatePartialOrd,
  )

  val zonePrec = { s : LazyS -> ZonePrec.of(getActiveClocks(s.concrState)) }
  val clockStrategy = when (lazyDomain.refinement) {
    LazyRefinement.BW_ITP -> BwItpStrategy(
      createLazyClockLens<ZoneState, ZoneState>() as Lens<LazyS, LazyState<ZoneState, ZoneState>>,
      ZoneLattice.getInstance(),
      ZoneInterpolator.getInstance(),
      BasicConcretizer.create(ZoneOrd.getInstance()),
      getClockActionInvTransFunc(XcfaZoneInvTransFunc()),
      zonePrec,
    )
    LazyRefinement.FW_ITP -> FwItpStrategy(
      createLazyClockLens<ZoneState, ZoneState>() as Lens<LazyS, LazyState<ZoneState, ZoneState>>,
      ZoneLattice.getInstance(),
      ZoneInterpolator.getInstance(),
      BasicConcretizer.create(ZoneOrd.getInstance()),
      getClockActionInvTransFunc(XcfaZoneInvTransFunc()),
      zonePrec,
      getClockActionTransFunc(XcfaZoneTransFunc()),
    )
    LazyRefinement.LU -> LuZoneStrategy(
      createAbstrClockLens<LuZoneState>() as Lens<LazyS, LuZoneState>,
      { bounds, action -> XcfaLuZonePre().pre(bounds, getClockAction(action)) },
    )
  }

  val lazyStrategy = Prod2LazyStrategy(
    createConcrProd2Lens<S, ZoneState>() as Lens<LazyS, Prod2State<S, ZoneState>>,
    dataStrategy,
    clockStrategy,
    { s ->
      Tuple4.of(
        s.concrState.processes.map { it.value.paramsInitialized },
        s.concrState.processes.map { it.value.locs.peek() },
        dataStrategy.projection.apply(s),
        clockStrategy.projection.apply(s)
      )
    }
  )

  ///

  val dataAnalysis = cegarDomain.analysis(
    abstractionSolver,
    True(),
    cegarConfig.abstractorConfig.maxEnum,
    xcfa
  ) as Analysis<S, XcfaAction, Prec>

  check(lazyDomain.concrDomain == TimeDomain.ZONE)
  val clockAnalysis = XcfaZoneAnalysis(xcfa)
    as Analysis<S, XcfaAction, Prec>

  val prod2Analysis = Prod2Analysis.create(
      dataAnalysis,
      clockAnalysis,
      DataClockXcfaActionSplitter
  ) as Analysis<ProdS, ExprAction, ProdP>

  val dataVarLookups : (XcfaS, XcfaAction) -> List<Map<VarDecl<*>, VarDecl<*>>> = cegarDomain.varLookups
  val xcfaAnalysis = XcfaAnalysis<ProdS, PtrP>(
    getXcfaPartialOrder(prod2Analysis.partialOrd.getPtrPartialOrd()),
    getXcfaInitFunc(xcfa, prod2Analysis.initFunc),
    getXcfaTransFunc(
      prod2Analysis.transFunc,
      { s, a, p -> (p.p as PtrPrec<Prod2Prec<Prec, ZonePrec>>).addVarsAndClocks(s, dataVarLookups(s, a)) as PtrP },
      cegarConfig.abstractorConfig.havocMemory
    ),
    coi
  )

  val lazyAnalysis : LazyAnalysis<XcfaS, XcfaS, XcfaAction, XcfaP> = LazyAnalysis.create(
    xcfaAnalysis.partialOrd,
    xcfaAnalysis.initFunc,
    xcfaAnalysis.transFunc,
    XcfaInitAbstractor(lazyStrategy.initAbstractor) as InitAbstractor<XcfaS, XcfaS>
  )

  ///

  val errorDetector = getXcfaErrorDetector(config.inputConfig.property.verifiedProperty)

  val lazyAbstractor = LazyAbstractor<ProdS, ProdS, XcfaS, XcfaS, XcfaAction, XcfaP>(
    lts as LTS<XcfaS, XcfaAction>,
    waitlist as Waitlist<ArgNode<LazyS, XcfaAction>>,
    lazyStrategy as LazyStrategy<ProdS, ProdS, LazyS, XcfaAction>,
    lazyAnalysis,
    { s -> errorDetector.test(s) },
    createConcrProd2Lens<S, S>() as Lens<LazyS, ProdS>,
    logger,
  ) as ArgAbstractor<ExprState, ExprAction, Prec>

  ///

  val traceChecker: ExprTraceChecker<Refutation> =
    errorDetector.exprTraceCheckerWrapper(
      cegarConfig.refinerConfig.refinement.refiner(
        refinementSolverFactory,
        cegarConfig.cexMonitor
      ) as ExprTraceChecker<Refutation>
    )

  val itpRefToDomainPrec = cegarDomain.itpRefToPrec(
    cegarConfig.refinerConfig.exprSplitter.exprSplitter, xcfa
  ) as RefutationToPrec<Prec, ItpRefutation>

  val xcfaPrecRefiner = XcfaPrecRefiner<PtrS, Prec, ItpRefutation>(
    ItpRefToPtrPrec(
      ItpRefToProd2DataZonePrec(
        itpRefToDomainPrec
      ) as RefutationToPrec<Prec, ItpRefutation>
    )
  ) as PrecRefiner<XcfaS, XcfaAction, XcfaP, ItpRefutation>

  val concrTracePrecRefiner = PrecRefiner<LazyS, XcfaAction, XcfaP, ItpRefutation> { prec, trace, refutation ->
    xcfaPrecRefiner.refine(
      prec,
      Trace.of(trace.states.map { it.concrState }, trace.actions),
      refutation
    )
  } as PrecRefiner<ExprState, ExprAction, Prec, Refutation>

  val atomicNodePruner: NodePruner<ExprState, ExprAction> =
    AtomicNodePruner<XcfaS, XcfaAction>() as NodePruner<ExprState, ExprAction>
  val refiner: ArgRefiner<ExprState, ExprAction, Prec> =
    if (cegarConfig.refinerConfig.refinement == Refinement.MULTI_SEQ)
      if (cegarConfig.por == POR.AASPOR)
        MultiExprTraceRefiner.create(
          traceChecker,
          concrTracePrecRefiner,
          cegarConfig.refinerConfig.pruneStrategy,
          logger,
          atomicNodePruner,
        )
      else
        MultiExprTraceRefiner.create(
          traceChecker,
          concrTracePrecRefiner,
          cegarConfig.refinerConfig.pruneStrategy,
          logger,
        )
    else if (cegarConfig.por == POR.AASPOR)
      XcfaSingleExprTraceRefiner.create(
        traceChecker,
        concrTracePrecRefiner,
        cegarConfig.refinerConfig.pruneStrategy,
        logger,
        atomicNodePruner,
        createConcrLens() as Lens<ExprState, XcfaState<PtrState<*>>>,
      )
    else
      XcfaSingleExprTraceRefiner.create(
        traceChecker,
        concrTracePrecRefiner,
        cegarConfig.refinerConfig.pruneStrategy,
        logger,
        createConcrLens() as Lens<ExprState, XcfaState<PtrState<*>>>,
      )

  ///

  val cegarChecker =
    if (cegarConfig.por == POR.AASPOR)
      ArgCegarChecker.create(
        lazyAbstractor,
        AasporRefiner.create(refiner, cegarConfig.refinerConfig.pruneStrategy, ignoredVarRegistry),
        logger,
      )
    else ArgCegarChecker.create(lazyAbstractor, refiner, logger)

  // initialize monitors
  MonitorCheckpoint.reset()
  if (cegarConfig.cexMonitor == CexMonitorOptions.CHECK) {
    val cm = CexMonitor(logger, cegarChecker.proof)
    MonitorCheckpoint.register(cm, "CegarChecker.unsafeARG")
  }

  return object : SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {

    override fun check():
      SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>> {
      val initXcfaPrec = cegarDomain.initPrec(xcfa, cegarConfig.initPrec)
      val initPtrPrec = initXcfaPrec.p
      
      val initDataPrec = initPtrPrec.innerPrec
      val initZonePrec = ZonePrec.of(
        xcfa.initProcedures.flatMap { it.first.clocks }
        + xcfa.clocks.map { cast(it.wrappedVar, Rat()) }
      )

      val initPrec = XcfaPrec(
        p = PtrPrec(
          innerPrec = Prod2Prec.of(initDataPrec, initZonePrec),
          set = initPtrPrec.set,
          smth = initPtrPrec.smth,
        ),
        noPop = initXcfaPrec.noPop,
      )
      return check(initPrec)
    }

    override fun check(
      prec: XcfaPrec<*>?
    ): SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>> {

      val ret = cegarChecker.check(prec)

      val toAbstrXcfaState = { s : ExprState -> (s as LazyS).abstrState as XcfaState<PtrState<*>> }
      if (ret.isSafe) {
        return safeCegarResult(ret.asSafe().proof, xcfa, toAbstrXcfaState)
      } else {
        return unsafeCegarResult(ret.asUnsafe().cex, toAbstrXcfaState)
      }
    }
  }
}
