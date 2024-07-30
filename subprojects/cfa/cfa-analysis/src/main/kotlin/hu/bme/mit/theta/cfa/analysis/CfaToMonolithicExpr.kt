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

package hu.bme.mit.theta.cfa.analysis;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import java.util.*

fun CFA.toMonolithicExpr(): MonolithicExpr {
    Preconditions.checkArgument(this.errorLoc.isPresent);

    val map = mutableMapOf<CFA.Loc, Int>()
    for ((i, x) in this.locs.withIndex()) {
        map[x] = i;
    }
    val locVar = Decls.Var("__loc__", Int())
    val tranList = this.edges.map { e ->
        SequenceStmt.of(listOf(
            AssumeStmt.of(Eq(locVar.ref, Int(map[e.source]!!))),
            e.stmt,
            AssignStmt.of(locVar, Int(map[e.target]!!))
        ))
    }.toList()
    val trans = NonDetStmt.of(tranList);
    val transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0));
    val transExpr = And(transUnfold.exprs)
    val initExpr = Eq(locVar.ref, Int(map[this.initLoc]!!))
    val propExpr = Neq(locVar.ref, Int(map[this.errorLoc.orElseThrow()]!!))

    val offsetIndex = transUnfold.indexing

    return MonolithicExpr(initExpr, transExpr, propExpr, offsetIndex)
}

fun CFA.valToAction(val1: Valuation, val2: Valuation): CfaAction {
    val val1Map = val1.toMap()
    val val2Map = val2.toMap()
    var i = 0
    val map: MutableMap<CFA.Loc, Int> = mutableMapOf()
    for (x in this.locs) {
        map[x] = i++
    }
    return CfaAction.create(
        this.edges.first { edge ->
            map[edge.source] == (val1Map[val1Map.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt() &&
                map[edge.target] == (val2Map[val2Map.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt()
        })
}

fun CFA.valToState(val1: Valuation): CfaState<ExplState> {
    val valMap = val1.toMap()
    var i = 0
    val map: MutableMap<Int, CFA.Loc> = mutableMapOf()
    for (x in this.locs) {
        map[i++] = x
    }
    return CfaState.of(
        map[(valMap[valMap.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt()],
        ExplState.of(val1)
    )
}

