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
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr
import hu.bme.mit.theta.core.type.enumtype.EnumType
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import java.util.*

fun CFA.toMonolithicExpr(): MonolithicExpr {
    Preconditions.checkArgument(this.errorLoc.isPresent);
    val enumType = EnumType.of("locType", this.locs.map { it.name }.toList())

    val locVar = Decls.Var("__loc__", enumType)
    val tranList = this.edges.map { e ->
        SequenceStmt.of(listOf(
            AssumeStmt.of(Eq(locVar.ref, EnumLitExpr.of(enumType, e.source.name))),
            e.stmt,
            AssignStmt.of(locVar, EnumLitExpr.of(enumType, e.target.name))
        ))
    }.toList()
    val trans = NonDetStmt.of(tranList);
    val transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0));
    val transExpr = And(transUnfold.exprs)
    val initExpr = Eq(locVar.ref, EnumLitExpr.of(enumType, this.initLoc.name))
    val propExpr = Neq(locVar.ref, EnumLitExpr.of(enumType, this.errorLoc.orElseThrow().name))

    val offsetIndex = transUnfold.indexing

    return MonolithicExpr(initExpr, transExpr, propExpr, offsetIndex, ctrlVars = listOf(locVar))
}

fun CFA.valToAction(val1: Valuation, val2: Valuation): CfaAction {
    val val1Map = val1.toMap()
    val val2Map = val2.toMap()

    return CfaAction.create(
        this.edges.first { edge ->
            edge.source.name == (val1Map[val1Map.keys.first { it.name == "__loc__" }] as EnumLitExpr).value &&
                edge.target.name == (val2Map[val2Map.keys.first { it.name == "__loc__" }] as EnumLitExpr).value
        })
}

fun CFA.valToState(val1: Valuation): CfaState<ExplState> {
    val valMap = val1.toMap()

    return CfaState.of(
        this.locs.first {
            it.name == (valMap[valMap.keys.first { it.name == "__loc__" }] as EnumLitExpr).value
        },
        ExplState.of(val1)
    )
}

