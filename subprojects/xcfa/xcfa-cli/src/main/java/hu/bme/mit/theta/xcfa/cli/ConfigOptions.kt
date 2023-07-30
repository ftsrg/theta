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

package hu.bme.mit.theta.xcfa.cli

import com.google.gson.reflect.TypeToken
import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.ArgNode
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.ArgNodeComparator
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
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
import hu.bme.mit.theta.analysis.waitlist.Waitlist
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.*
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
    CHC
}

enum class Backend {
    CEGAR,
    BMC,
    LAZY
}

enum class POR(
    val getLts: (XCFA, MutableMap<Decl<out hu.bme.mit.theta.core.type.Type>, MutableSet<ExprState>>) -> LTS<XcfaState<out ExprState>, XcfaAction>,
    val isDynamic: Boolean
) {

    NOPOR({ _, _ -> getXcfaLts() }, false),
    SPOR({ xcfa, _ -> XcfaSporLts(xcfa) }, false),
    AASPOR({ xcfa, registry -> XcfaAasporLts(xcfa, registry) }, false),
    DPOR({ xcfa, _ -> XcfaDporLts(xcfa) }, true),
    AADPOR({ xcfa, _ -> XcfaAadporLts(xcfa) }, true)
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
        waitlist: Waitlist<out ArgNode<out XcfaState<out ExprState>, XcfaAction>>,
        stopCriterion: StopCriterion<out XcfaState<out ExprState>, XcfaAction>,
        logger: Logger,
        lts: LTS<XcfaState<out ExprState>, XcfaAction>,
        errorDetectionType: ErrorDetection,
        partialOrd: PartialOrd<out XcfaState<out ExprState>>
    ) -> Abstractor<out ExprState, out ExprAction, out Prec>,
    val itpPrecRefiner: (exprSplitter: ExprSplitter) -> PrecRefiner<out ExprState, out ExprAction, out Prec, out Refutation>,
    val initPrec: (XCFA, InitPrec) -> XcfaPrec<*>,
    val partialOrd: (Solver) -> PartialOrd<out XcfaState<out ExprState>>,
    val nodePruner: NodePruner<out ExprState, out ExprAction>,
    val stateType: Type
) {

    EXPL(
        abstractor = { a, b, c, d, e, f, g, h, i ->
            getXcfaAbstractor(ExplXcfaAnalysis(a, b, c, i as PartialOrd<XcfaState<ExplState>>), d,
                e, f, g, h)
        },
        itpPrecRefiner = {
            XcfaPrecRefiner<ExplState, ExplPrec, ItpRefutation>(ItpRefToExplPrec())
        },
        initPrec = { x, ip -> ip.explPrec(x) },
        partialOrd = { getPartialOrder<ExplState> { s1, s2 -> s1.isLeq(s2) } },
        nodePruner = AtomicNodePruner<XcfaState<ExplState>, XcfaAction>(),
        stateType = TypeToken.get(ExplState::class.java).type
    ),
    PRED_BOOL(
        abstractor = { a, b, c, d, e, f, g, h, i ->
            getXcfaAbstractor(PredXcfaAnalysis(a, b, PredAbstractors.booleanAbstractor(b),
                i as PartialOrd<XcfaState<PredState>>), d, e, f, g, h)
        },
        itpPrecRefiner = { a ->
            XcfaPrecRefiner<PredState, PredPrec, ItpRefutation>(ItpRefToPredPrec(a))
        },
        initPrec = { x, ip -> ip.predPrec(x) },
        partialOrd = { solver -> getPartialOrder<PredState>(PredOrd.create(solver)) },
        nodePruner = AtomicNodePruner<XcfaState<PredState>, XcfaAction>(),
        stateType = TypeToken.get(PredState::class.java).type
    ),
    PRED_CART(
        abstractor = { a, b, c, d, e, f, g, h, i ->
            getXcfaAbstractor(PredXcfaAnalysis(a, b, PredAbstractors.cartesianAbstractor(b),
                i as PartialOrd<XcfaState<PredState>>), d, e, f, g, h)
        },
        itpPrecRefiner = { a ->
            XcfaPrecRefiner<PredState, PredPrec, ItpRefutation>(ItpRefToPredPrec(a))
        },
        initPrec = { x, ip -> ip.predPrec(x) },
        partialOrd = { solver -> getPartialOrder<PredState>(PredOrd.create(solver)) },
        nodePruner = AtomicNodePruner<XcfaState<PredState>, XcfaAction>(),
        stateType = TypeToken.get(PredState::class.java).type
    ),
    PRED_SPLIT(
        abstractor = { a, b, c, d, e, f, g, h, i ->
            getXcfaAbstractor(PredXcfaAnalysis(a, b, PredAbstractors.booleanSplitAbstractor(b),
                i as PartialOrd<XcfaState<PredState>>), d, e, f, g, h)
        },
        itpPrecRefiner = { a ->
            XcfaPrecRefiner<PredState, PredPrec, ItpRefutation>(ItpRefToPredPrec(a))
        },
        initPrec = { x, ip -> ip.predPrec(x) },
        partialOrd = { solver -> getPartialOrder<PredState>(PredOrd.create(solver)) },
        nodePruner = AtomicNodePruner<XcfaState<PredState>, XcfaAction>(),
        stateType = TypeToken.get(PredState::class.java).type
    ),
}

enum class Refinement(
    val refiner: (solverFactory: SolverFactory) -> ExprTraceChecker<out Refutation>,
    val stopCriterion: StopCriterion<XcfaState<out ExprState>, XcfaAction>
) {

    FW_BIN_ITP(
        refiner = { s ->
            ExprTraceFwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(), s.createItpSolver())
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    BW_BIN_ITP(
        refiner = { s ->
            ExprTraceBwBinItpChecker.create(BoolExprs.True(), BoolExprs.True(), s.createItpSolver())
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    SEQ_ITP(
        refiner = { s ->
            ExprTraceSeqItpChecker.create(BoolExprs.True(), BoolExprs.True(), s.createItpSolver())
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    MULTI_SEQ(
        refiner = { s ->
            ExprTraceSeqItpChecker.create(BoolExprs.True(), BoolExprs.True(), s.createItpSolver())
        },
        stopCriterion = StopCriterions.fullExploration()
    ),
    UNSAT_CORE(
        refiner = { s ->
            ExprTraceUnsatCoreChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    UCB(
        refiner = { s ->
            ExprTraceUCBChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
        },
        stopCriterion = StopCriterions.firstCex()
    ),

    NWT_SP(
        refiner = { s ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withoutIT().withSP().withoutLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_WP(
        refiner = { s ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withoutIT().withWP().withoutLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_SP_LV(
        refiner = { s ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withoutIT().withSP().withLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_WP_LV(
        refiner = { s ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withoutIT().withWP().withLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_IT_WP(
        refiner = { s ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withIT().withWP().withoutLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_IT_SP(
        refiner = { s ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withIT().withSP().withoutLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_IT_WP_LV(
        refiner = { s ->
            ExprTraceNewtonChecker.create(BoolExprs.True(), BoolExprs.True(), s.createUCSolver())
                .withIT().withWP().withLV()
        },
        stopCriterion = StopCriterions.firstCex()
    ),
    NWT_IT_SP_LV(
        refiner = { s ->
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
            return ArgNodeComparators.combine(ArgNodeComparators.targetFirst(),
                ArgNodeComparators.bfs())
        }
    },
    DFS {

        override fun getComp(cfa: XCFA): ArgNodeComparator {
            return ArgNodeComparators.combine(ArgNodeComparators.targetFirst(),
                ArgNodeComparators.dfs())
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
    val explPrec: (xcfa: XCFA) -> XcfaPrec<ExplPrec>,
    val predPrec: (xcfa: XCFA) -> XcfaPrec<PredPrec>,
) {

    EMPTY(
        explPrec = { XcfaPrec(ExplPrec.empty()) },
        predPrec = { XcfaPrec(PredPrec.of()) }
    ),
    ALLVARS(
        explPrec = { xcfa -> XcfaPrec(ExplPrec.of(xcfa.collectVars())) },
        predPrec = { error("ALLVARS is not interpreted for the predicate domain.") }
    ),
    ALLGLOBALS(
        explPrec = { xcfa -> XcfaPrec(ExplPrec.of(xcfa.vars.map { it.wrappedVar })) },
        predPrec = { error("ALLGLOBALS is not interpreted for the predicate domain.") }
    ),
    ALLASSUMES(
        explPrec = { error("ALLVARS is not interpreted for the predicate domain.") },
        predPrec = { xcfa -> XcfaPrec(PredPrec.of(xcfa.collectAssumes())) },
    ),

}

// TODO CexMonitor: disable for multi_seq?
enum class CexMonitorOptions {

    CHECK,
    MITIGATE,
    DISABLE
}
