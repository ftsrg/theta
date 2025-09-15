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
package hu.bme.mit.theta.xsts.analysis

import hu.bme.mit.theta.core.Relation
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.plus
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.PrimeExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.enumtype.EnumEqExpr
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr
import hu.bme.mit.theta.core.type.enumtype.EnumNeqExpr
import hu.bme.mit.theta.core.type.enumtype.EnumType
import hu.bme.mit.theta.core.type.inttype.IntEqExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntNeqExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.xsts.XSTS
import java.math.BigInteger

fun XSTS.toRelations(): List<Relation> {
  val enumValueLut = LinkedHashMap<EnumType, MutableMap<String, Int>>()
  val varChangeMap = LinkedHashMap<VarDecl<*>, VarDecl<*>>()
  var cnt = 0
  fun Expr<*>.replaceEnums(): Expr<*> {
    if (type is EnumType) {
      when (this) {
        is EnumLitExpr -> {
          val value =
            enumValueLut
              .computeIfAbsent(this.type) { LinkedHashMap() }
              .computeIfAbsent(this.value) { cnt++ }
          return IntLitExpr.of(BigInteger.valueOf(value.toLong()))
        }

        is RefExpr -> {
          return varChangeMap.computeIfAbsent(decl as VarDecl) { Var(this.decl.name, Int()) }.ref
        }

        is PrimeExpr -> {
          return PrimeExpr.of(op.replaceEnums())
        }

        else -> error("I expect that only EnumLiterals and RefExprs may have EnumType")
      }
    } else if (this is EnumEqExpr) {
      return IntEqExpr.of(
        leftOp.replaceEnums() as Expr<IntType>,
        rightOp.replaceEnums() as Expr<IntType>,
      )
    } else if (this is EnumNeqExpr) {
      return IntNeqExpr.of(
        leftOp.replaceEnums() as Expr<IntType>,
        rightOp.replaceEnums() as Expr<IntType>,
      )
    } else {
      return this.map(Expr<*>::replaceEnums)
    }
  }

  fun VarIndexing.replaceEnums() = transform().copyVars(varChangeMap).build()

  val initUnfoldResult = StmtUtils.toExpr(this.init, VarIndexingFactory.indexing(0))
  val initExpr = And(And(initUnfoldResult.exprs), this.initFormula).replaceEnums() as Expr<BoolType>
  val initOffsetIndex = initUnfoldResult.indexing.replaceEnums()

  val envUnfoldResult = StmtUtils.toExpr(env, VarIndexingFactory.indexing(0))
  val envExpr = And(envUnfoldResult.exprs).replaceEnums() as Expr<BoolType>
  val envOffsetIndex = envUnfoldResult.indexing.replaceEnums()

  val tranUnfoldResult = StmtUtils.toExpr(tran, VarIndexingFactory.indexing(0))
  val tranExpr = And(tranUnfoldResult.exprs).replaceEnums() as Expr<BoolType>
  val tranOffsetIndex = tranUnfoldResult.indexing.replaceEnums()

  val propExpr = this.prop.replaceEnums() as Expr<BoolType>

  val vars = vars.map { varChangeMap[it] ?: it }

  val types = vars.map { it.type }.toTypedArray()
  val oldParams = vars.associateWith { Param("|" + it.name + "|", it.type) }
  val oldParamList = vars.map { oldParams[it]!!.ref }.toTypedArray()
  val newParams = vars.associateWith { Param("|" + it.name + "_new|", it.type) }

  fun toRelation(
    rel: Relation,
    prevRels: List<Relation>,
    notUnfoldedExpr: Expr<BoolType>,
    indexing: VarIndexing,
    vars: List<VarDecl<*>>,
  ): Relation {

    val expr = PathUtils.unfold(notUnfoldedExpr, VarIndexingFactory.indexing(0))

    // var[0] is oldParam, var[-1]is newParam, everything else is a fresh param
    var cnt = 0
    val consts =
      ExprUtils.getIndexedConstants(expr).associateWith {
        if (it.index == 0 && oldParams.containsKey(it.varDecl)) oldParams[it.varDecl]!!
        else if (it.index == indexing[it.varDecl] && newParams.containsKey(it.varDecl))
          newParams[it.varDecl]!!
        else Param("__tmp_${cnt++}", it.type)
      }
    val newParamList =
      vars
        .map { if (indexing[it] == 0) oldParams[it]!!.ref else newParams[it]!!.ref }
        .toTypedArray()
    val paramdExpr = ExprUtils.changeDecls(expr, consts)
    if (prevRels.isEmpty()) {
      rel(*newParamList) += paramdExpr
    } else {
      for (prevRel in prevRels) {
        rel(*newParamList) += prevRel(*oldParamList).expr + paramdExpr
      }
    }
    return rel
  }

  val init = Relation("init", *types)
  val env = Relation("env", *types)
  val tran = Relation("tran", *types)

  toRelation(init, listOf(), initExpr, initOffsetIndex, vars.toList())
  toRelation(env, listOf(init, tran), envExpr, envOffsetIndex, vars.toList())
  toRelation(tran, listOf(env), tranExpr, tranOffsetIndex, vars.toList())
  !(tran(*oldParamList) with ExprUtils.changeDecls(Not(propExpr), oldParams))

  return listOf(init, tran, env)
}
