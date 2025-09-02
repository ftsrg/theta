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
package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.common.container.Containers
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.fptype.FpExprs
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import java.util.*

private val reprEq = { e1: Expr<*>, e2: Expr<*> ->
  if (e1.type is FpType) FpExprs.FpAssign(e1 as Expr<FpType>, e2 as Expr<FpType>) else Eq(e1, e2)
}

fun MonolithicExpr.createMonolithicL2S(): MonolithicExpr {
  val saved = Decls.Var("__saved_", BoolType.getInstance())
  val saveMap: MutableMap<VarDecl<*>, VarDecl<*>> = HashMap()
  val tmpVars: Set<VarDecl<*>> = Containers.createSet()
  ExprUtils.collectVars(initExpr, tmpVars)
  ExprUtils.collectVars(transExpr, tmpVars)
  ExprUtils.collectVars(propExpr, tmpVars)
  val vars = Collections.unmodifiableCollection(tmpVars)
  for (varDecl in vars) {
    val newVar: VarDecl<*> = Decls.Var("__saved_" + varDecl.name, varDecl.type)
    saveMap[varDecl] = newVar
  }
  val savedInitExpr = And(vars.map { reprEq(it.ref, saveMap[it]!!.ref) }.toList())

  val saveList = ArrayList<Expr<BoolType>>()
  val skipList = ArrayList<Expr<BoolType>>()
  val indx = VarIndexingFactory.indexing(1)

  // New transition expr
  for ((key, value) in saveMap.entries) {
    saveList.add(reprEq(ExprUtils.applyPrimes(value.ref, indx), key.ref))
  }
  for (varDecl in saveMap.values) {
    skipList.add(reprEq(ExprUtils.applyPrimes(varDecl.ref, indx), varDecl.ref))
  }

  skipList.add(reprEq(ExprUtils.applyPrimes(saved.ref, indx), saved.ref))
  saveList.add(reprEq(ExprUtils.applyPrimes(saved.ref, indx), BoolExprs.True()))
  val skipOrSave = SmartBoolExprs.Or(And(skipList), And(saveList))
  val newTransExpr = ArrayList<Expr<BoolType>>(setOf(transExpr))
  newTransExpr.add(skipOrSave)

  // New prop expr
  var prop: Expr<BoolType> = saved.ref
  for ((key, value) in saveMap) {
    val exp = reprEq(value.ref, key.ref)
    prop = And(exp, prop)
  }

  // New offset
  var newIndexing: VarIndexing = transOffsetIndex
  for (varDecl in saveMap.values) {
    newIndexing = newIndexing.inc(varDecl, 1)
  }
  newIndexing = newIndexing.inc(saved, 1)

  return MonolithicExpr(
    initExpr = And(initExpr, Not(saved.ref), savedInitExpr),
    transExpr = And(newTransExpr),
    propExpr = Not(And(prop, propExpr)),
    transOffsetIndex = newIndexing,
    initOffsetIndex = initOffsetIndex,
    valToState = { valuation -> valToState(valuation.filterVars(vars)) },
    biValToAction = { valuation1, valuation2 ->
      biValToAction(valuation1.filterVars(vars), valuation2.filterVars(vars))
    },
    ctrlVars = ctrlVars + ctrlVars.map { saveMap[it]!! } + saved,
  )
}
