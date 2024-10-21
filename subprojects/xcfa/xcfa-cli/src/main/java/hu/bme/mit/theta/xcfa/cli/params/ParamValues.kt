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

package hu.bme.mit.theta.xcfa.cli.params

import com.google.gson.reflect.TypeToken
import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNodeComparators
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNodeComparators.ArgNodeComparator
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterion
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.pred.*
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter
import hu.bme.mit.theta.analysis.ptr.ItpRefToPtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.ptr.getPtrPartialOrd
import hu.bme.mit.theta.analysis.waitlist.Waitlist
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.analysis.coi.ConeOfInfluence
import hu.bme.mit.theta.xcfa.analysis.por.*
import hu.bme.mit.theta.xcfa.cli.utils.XcfaDistToErrComparator
import hu.bme.mit.theta.xcfa.collectAssumes
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.model.XCFA
import java.lang.reflect.Type

enum class InputType {
    C,
    LLVM,
    JSON,
    DSL,
    CHC,
    LITMUS,
}

enum class Backend {
    CEGAR,
    BOUNDED,
    CHC,
    OC,
    LAZY,
    PORTFOLIO,
    NONE,
}

enum class POR(
    val getLts: (XCFA, MutableMap<VarDecl<*>, MutableSet<ExprState>>) -> LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction>,
    val isDynamic: Boolean,
    val isAbstractionAware: Boolean
) {

    NOPOR({ _, _ -> getXcfaLts() }, false, false),
    SPOR({ xcfa, _ -> XcfaSporLts(xcfa) }, false, false),
    AASPOR({ xcfa, registry -> XcfaAasporLts(xcfa, registry) }, false, true),
    DPOR({ xcfa, _ -> XcfaDporLts(xcfa) }, true, false),
    AADPOR({ xcfa, _ -> XcfaAadporLts(xcfa) }, true, true)
}

enum class Strategy {
    DIRECT,
    SERVER,
    SERVER_DEBUG,
    PORTFOLIO
}

// TODO partial orders nicely
enum class Domain(
    val abstractor: (
        xcfa: XCFA,
        solver: Solver,
        maxEnum: Int,
        waitlist: Waitlist<out ArgNode<out XcfaState<out PtrState<out ExprState>>, XcfaAction>>,
        stopCriterion: StopCriterion<out XcfaState<out PtrState<out ExprState>>, XcfaAction>,
        logger: Logger,
        lts: LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction>,
        errorDetectionType: ErrorDetection,
        partialOrd: PartialOrd<out XcfaState<out PtrState<out ExprState>>>,
        isHavoc: Boolean
    ) -> ArgAbstractor<out ExprState, out ExprAction, out Prec>,
    val itpPrecRefiner: (exprSplitter: ExprSplitter) -> PrecRefiner<out ExprState, out ExprAction, out Prec, out Refutation>,
    val initPrec: (XCFA, InitPrec) -> XcfaPrec<out PtrPrec<*>>,
    val partialOrd: (Solver) -> PartialOrd<out PtrState<out ExprState>>,
    val nodePruner: NodePruner<out ExprState, out ExprAction>,
    val stateType: Type
) {

    EXPL(
        abstractor = { a, b, c, d, e, f, g, h, i, j ->
            getXcfaAbstractor(
                ExplXcfaAnalysis(a, b, c, i as PartialOrd<XcfaState<PtrState<ExplState>>>, j), d,
                e, f, g, h
            )
        },
        itpPrecRefiner = {
            XcfaPrecRefiner<PtrState<ExplState>, ExplPrec, ItpRefutation>(ItpRefToPtrPrec(ItpRefToExplPrec()))
        },
        initPrec = { x, ip -> ip.explPrec(x) },
        partialOrd = { PartialOrd<ExplState> { s1, s2 -> s1.isLeq(s2) }.getPtrPartialOrd() },
        nodePruner = AtomicNodePruner<XcfaState<PtrState<ExplState>>, XcfaAction>(),
        stateType = TypeToken.get(ExplState::class.java).type
    ),
    PRED_BOOL(
        abstractor = { a, b, c, d, e, f, g, h, i, j ->
            getXcfaAbstractor(
                PredXcfaAnalysis(
                    a, b, PredAbstractors.booleanAbstractor(b),
                    i as PartialOrd<XcfaState<PtrState<PredState>>>, j
                ), d, e, f, g, h
            )
        },
        itpPrecRefiner = { a ->
            XcfaPrecRefiner<PtrState<PredState>, PredPrec, ItpRefutation>(ItpRefToPtrPrec(ItpRefToPredPrec(a)))
        },
        initPrec = { x, ip -> ip.predPrec(x) },
        partialOrd = { solver -> PredOrd.create(solver).getPtrPartialOrd() },
        nodePruner = AtomicNodePruner<XcfaState<PtrState<PredState>>, XcfaAction>(),
        stateType = TypeToken.get(PredState::class.java).type
    ),
    PRED_CART(
        abstractor = { a, b, c, d, e, f, g, h, i, j ->
            getXcfaAbstractor(
                PredXcfaAnalysis(
                    a, b, PredAbstractors.cartesianAbstractor(b),
                    i as PartialOrd<XcfaState<PtrState<PredState>>>, j
                ), d, e, f, g, h
            )
        },
        itpPrecRefiner = { a ->
            XcfaPrecRefiner<PtrState<PredState>, PredPrec, ItpRefutation>(ItpRefToPtrPrec(ItpRefToPredPrec(a)))
        },
        initPrec = { x, ip -> ip.predPrec(x) },
        partialOrd = { solver -> PredOrd.create(solver).getPtrPartialOrd() },
        nodePruner = AtomicNodePruner<XcfaState<PtrState<PredState>>, XcfaAction>(),
        stateType = TypeToken.get(PredState::class.java).type
    ),
    PRED_SPLIT(
        abstractor = { a, b, c, d, e, f, g, h, i, j ->
            getXcfaAbstractor(
                PredXcfaAnalysis(
                    a, b, PredAbstractors.booleanSplitAbstractor(b),
                    i as PartialOrd<XcfaState<PtrState<PredState>>>, j
                ), d, e, f, g, h
            )
        },
        itpPrecRefiner = { a ->
            XcfaPrecRefiner<PtrState<PredState>, PredPrec, ItpRefutation>(ItpRefToPtrPrec(ItpRefToPredPrec(a)))
        },
        initPrec = { x, ip -> ip.predPrec(x) },
        partialOrd = { solver -> PredOrd.create(solver).getPtrPartialOrd() },
        nodePruner = AtomicNodePruner<XcfaState<PtrState<PredState>>, XcfaAction>(),
        stateType = TypeToken.get(PredState::class.java).type
    ),
}

enum class Refinement(
    val refiner: (solverFactory: SolverFactory, monitorOption: CexMonitorOptions) -> ExprTraceChecker<out Refutation>,
    val stopCriterion: StopCriterion<XcfaState<PtrState<ExprState>>, XcfaAction>,
) {

    FW_BIN_ITP(
        refiner = { s, _ ->
            ExprTraceFwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(), s.createItpSolver())
        },
        stopCriterion = StopCriterions.firstCex(),
    ),
    BW_BIN_ITP(
        refiner = { s, _ ->
            ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(), s.createItpSolver())
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    SEQ_ITP(
        refiner = { s, _ ->
            ExprTraceSeqItpChecker.create(BoolExprs.True(), BoolExprs.True(), s.createItpSolver())
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    MULTI_SEQ(
        refiner = { s, m ->
            if (m == CexMonitorOptions.CHECK) error("CexMonitor is not implemented for MULTI_SEQ")
            ExprTraceSeqItpChecker.create(BoolExprs.True(), BoolExprs.True(), s.createItpSolver())
        },
        stopCriterion = StopCriterions.fullExploration()
    ),
    UNSAT_CORE(
        refiner = { s, _ ->
            ExprTraceUnsatCoreChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    UCB(
        refiner = { s, _ ->
            ExprTraceUCBChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
        },
        stopCriterion = StopCriterions.firstCex()
    ),

    NWT_SP(
        refiner = { s, _ ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withoutIT().withSP().withoutLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_WP(
        refiner = { s, _ ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withoutIT().withWP().withoutLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_SP_LV(
        refiner = { s, _ ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withoutIT().withSP().withLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_WP_LV(
        refiner = { s, _ ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withoutIT().withWP().withLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_IT_WP(
        refiner = { s, _ ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withIT().withWP().withoutLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_IT_SP(
        refiner = { s, _ ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withIT().withSP().withoutLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_IT_WP_LV(
        refiner = { s, _ ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withIT().withWP().withLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_IT_SP_LV(
        refiner = { s, _ ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withIT().withSP().withLV()
        },
        stopCriterion = StopCriterions.firstCex()
    )
}


enum class ExprSplitterOptions(val exprSplitter: ExprSplitter) {
    WHOLE(ExprSplitters.whole()),
    CONJUNCTS(ExprSplitters.conjuncts()),
    ATOMS(ExprSplitters.atoms());
}

enum class Search {
    BFS {

        override fun getComp(cfa: XCFA): ArgNodeComparator {
            return ArgNodeComparators.combine(
                ArgNodeComparators.targetFirst(),
                ArgNodeComparators.bfs()
            )
        }
    },
    DFS {

        override fun getComp(cfa: XCFA): ArgNodeComparator {
            return ArgNodeComparators.combine(
                ArgNodeComparators.targetFirst(),
                ArgNodeComparators.dfs()
            )
        }
    },
    ERR {

        override fun getComp(cfa: XCFA): ArgNodeComparator {
            return XcfaDistToErrComparator(cfa)
        }
    };

    abstract fun getComp(cfa: XCFA): ArgNodeComparator
}

enum class InitPrec(
    val explPrec: (xcfa: XCFA) -> XcfaPrec<PtrPrec<ExplPrec>>,
    val predPrec: (xcfa: XCFA) -> XcfaPrec<PtrPrec<PredPrec>>,
) {

    EMPTY(
        explPrec = { XcfaPrec(PtrPrec(ExplPrec.empty(), emptySet())) },
        predPrec = { XcfaPrec(PtrPrec(PredPrec.of(), emptySet())) }
    ),
    ALLVARS(
        explPrec = { xcfa -> XcfaPrec(PtrPrec(ExplPrec.of(xcfa.collectVars()), emptySet())) },
        predPrec = { error("ALLVARS is not interpreted for the predicate domain.") }
    ),
    ALLGLOBALS(
        explPrec = { xcfa -> XcfaPrec(PtrPrec(ExplPrec.of(xcfa.vars.map { it.wrappedVar }), emptySet())) },
        predPrec = { error("ALLGLOBALS is not interpreted for the predicate domain.") }
    ),
    ALLASSUMES(
        explPrec = { xcfa ->
            XcfaPrec(
                PtrPrec(ExplPrec.of(xcfa.collectAssumes().flatMap(ExprUtils::getVars)), emptySet())
            )
        },
        predPrec = { xcfa -> XcfaPrec(PtrPrec(PredPrec.of(xcfa.collectAssumes()), emptySet())) },
    ),

}

enum class ConeOfInfluenceMode(
    val getLts: (XCFA, MutableMap<VarDecl<*>, MutableSet<ExprState>>, POR) -> LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction>
) {

    NO_COI({ xcfa, ivr, por ->
        por.getLts(xcfa, ivr).also { NO_COI.porLts = it }
    }),
    COI({ xcfa, ivr, por ->
        ConeOfInfluence.coreLts = por.getLts(xcfa, ivr).also { COI.porLts = it }
        ConeOfInfluence.lts
    }),
    POR_COI({ xcfa, ivr, por ->
        ConeOfInfluence.coreLts = getXcfaLts()
        if (por.isAbstractionAware) XcfaAasporCoiLts(xcfa, ivr, ConeOfInfluence.lts)
        else XcfaSporCoiLts(xcfa, ConeOfInfluence.lts)
    }),
    POR_COI_POR({ xcfa, ivr, por ->
        ConeOfInfluence.coreLts = por.getLts(xcfa, ivr).also { POR_COI_POR.porLts = it }
        if (por.isAbstractionAware) XcfaAasporCoiLts(xcfa, ivr, ConeOfInfluence.lts)
        else XcfaSporCoiLts(xcfa, ConeOfInfluence.lts)
    })
    ;

    var porLts: LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction>? = null
}

// TODO CexMonitor: disable for multi_seq
// TODO add new monitor to xsts cli
enum class CexMonitorOptions {

    CHECK,
    DISABLE
}
