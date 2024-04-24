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

package hu.bme.mit.theta.xcfa.cli.checkers

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.BoundedChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Neq
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.params.BoundedConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.cli.utils.valToAction
import hu.bme.mit.theta.xcfa.cli.utils.valToState
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.stream.Collectors

fun getBoundedChecker(xcfa: XCFA, mcm: MCM,
    config: XcfaConfig<*, *>,
    logger: Logger): SafetyChecker<XcfaState<PtrState<*>>, XcfaAction, XcfaPrec<*>> {

    val boundedConfig = config.backendConfig.specConfig as BoundedConfig

    return BoundedChecker(
        monolithicExpr = getMonolithicExpr(xcfa),
        bmcSolver = getSolver(boundedConfig.bmcConfig.bmcSolver,
            boundedConfig.bmcConfig.validateBMCSolver).createSolver(),
        bmcEnabled = { !boundedConfig.bmcConfig.disable },
        lfPathOnly = { !boundedConfig.bmcConfig.nonLfPath },
        itpSolver = getSolver(boundedConfig.itpConfig.itpSolver,
            boundedConfig.itpConfig.validateItpSolver).createItpSolver(),
        imcEnabled = { !boundedConfig.itpConfig.disable },
        indSolver = getSolver(boundedConfig.indConfig.indSolver,
            boundedConfig.indConfig.validateIndSolver).createSolver(),
        kindEnabled = { !boundedConfig.indConfig.disable },
        valToState = { valToState(xcfa, it) },
        biValToAction = { val1, val2 -> valToAction(xcfa, val1, val2) },
        logger = logger
    ) as SafetyChecker<XcfaState<PtrState<*>>, XcfaAction, XcfaPrec<*>>

}

private fun getMonolithicExpr(xcfa: XCFA): MonolithicExpr {
    Preconditions.checkArgument(xcfa.initProcedures.size == 1)
    val proc = xcfa.initProcedures.stream().findFirst().orElse(null).first
    Preconditions.checkArgument(proc.edges.map { it.getFlatLabels() }.flatten().none { it !is StmtLabel })
    Preconditions.checkArgument(proc.errorLoc.isPresent)
    var i = 0
    val map: MutableMap<XcfaLocation, Int> = HashMap()
    for (x in proc.locs) {
        map[x] = i++
    }
    val locVar = Decls.Var("__loc_", IntExprs.Int())
    val tranList = proc.edges.stream().map { (source, target, label): XcfaEdge ->
        SequenceStmt.of(java.util.List.of(
            AssumeStmt.of(IntExprs.Eq(locVar.ref, IntExprs.Int(map[source]!!))),
            label.toStmt(),
            AssignStmt.of(locVar,
                IntExprs.Int(map[target]!!))
        ))
    }.collect(Collectors.toList())
    val trans = NonDetStmt.of(tranList as List<Stmt>)
    val transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0))

    return MonolithicExpr(
        initExpr = Eq(locVar.ref, IntExprs.Int(map[proc.initLoc]!!)),
        transExpr = And(transUnfold.exprs),
        propExpr = Neq(locVar.ref, IntExprs.Int(map[proc.errorLoc.get()]!!)),
        offsetIndex = transUnfold.indexing
    )
}