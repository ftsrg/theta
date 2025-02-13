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

package hu.bme.mit.theta.analysis.l2s

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory

fun MonolithicExpr.createMonolithicL2S(): MonolithicExpr {
    val saved = Decls.Var("saved", BoolType.getInstance());
    val saveList = ArrayList<Expr<BoolType>>()
    val skipList = ArrayList<Expr<BoolType>>()
    val saveMap: Map<VarDecl<*>, VarDecl<*>> = HashMap()
    val indx = VarIndexingFactory.indexing(1)

    // New transition expr
    for ((key, value) in saveMap.entries) {
        saveList.add(AbstractExprs.Eq(ExprUtils.applyPrimes(value.ref, indx), key.ref))
    }
    for (varDecl in saveMap.values) {
        skipList.add(AbstractExprs.Eq(ExprUtils.applyPrimes(varDecl.ref, indx), varDecl.ref))
    }

    skipList.add(AbstractExprs.Eq(ExprUtils.applyPrimes(saved.ref, indx), saved.ref))
    saveList.add(AbstractExprs.Eq(ExprUtils.applyPrimes(saved.ref, indx), BoolExprs.True()))
    val skipOrSave = SmartBoolExprs.Or(And(skipList), And(saveList))
    val newTransExpr = ArrayList<Expr<BoolType>>(
        setOf(transExpr)
    )
    newTransExpr.add(skipOrSave)

    // New prop expr
    var prop: Expr<BoolType?>? = saved.ref
    for ((key, value) in saveMap) {
        val exp = AbstractExprs.Eq(value.ref, key.ref)
        prop = And(exp, prop)
    }

    // New offset
    var newIndexing: VarIndexing = transOffsetIndex
    for (varDecl in saveMap.values) {
        newIndexing = newIndexing.inc(varDecl, 1)
    }
    newIndexing = newIndexing.inc(saved, 1)

    return MonolithicExpr(
        initExpr = And(initExpr, Not(saved.ref)),
        transExpr = And(newTransExpr),
        propExpr = Not(And(prop, propExpr)),
        transOffsetIndex = newIndexing
    )
}