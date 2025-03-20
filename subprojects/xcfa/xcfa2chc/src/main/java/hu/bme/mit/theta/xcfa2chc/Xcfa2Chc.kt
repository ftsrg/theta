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
package hu.bme.mit.theta.xcfa2chc

import hu.bme.mit.theta.core.Relation
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.plus
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Add
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager
import hu.bme.mit.theta.xcfa.AssignStmtLabel
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

enum class RankingFunction(val constraint: (Expr<IntType>, Expr<IntType>) -> Expr<BoolType>) {
  ADD({ old, new -> Eq(new, Add(old, Int(1))) }) // +1
}

fun XcfaProcedure.toCHC(
  termination: Boolean = false,
  rankingFuncConstr: RankingFunction = RankingFunction.ADD,
): Pair<List<VarDecl<*>>, List<Relation>> {
  val vars = edges.flatMap { it.label.collectVars() }.toSet().toMutableList()

  val rankingFunction = Var("__ranking_func", Int())
  val havocArrays =
    edges
      .flatMap { it.label.getFlatLabels() }
      .mapNotNull { ((it as? StmtLabel)?.stmt as? HavocStmt<*>)?.varDecl?.type }
      .associateWith { Var("__nondet_array_${it}", ArrayType.of(Int(), it)) }

  if (termination) {
    vars.add(rankingFunction)
    vars.addAll(havocArrays.values)
  }

  val types = vars.map { it.type }.toTypedArray()
  val oldParams = vars.associateWith { Param("|" + it.name + "|", it.type) }
  val oldParamList = vars.map { oldParams[it]!!.ref }.toTypedArray()
  val newParams = vars.associateWith { Param("|" + it.name + "_new|", it.type) }

  val ufs = locs.associateWith { Relation(it.name, *types) }

  edges.forEach {
    val stmts =
      if (termination) {
          val labels = it.label.getFlatLabels()
          val newLabels = ArrayList<XcfaLabel>()
          if (it.source.initial) {
            newLabels.add(AssignStmtLabel(rankingFunction, Int(0)))
          }
          for (label in labels) {
            if (label is StmtLabel && label.stmt is HavocStmt<*>) {
              val havoc = (label.stmt as HavocStmt<*>)
              newLabels.add(
                AssignStmtLabel(
                  havoc.varDecl,
                  Read(havocArrays[havoc.varDecl.type]!!.ref, rankingFunction.ref),
                )
              )
            } else {
              newLabels.add(label)
            }
          }
          newLabels
        } else {
          it.label.getFlatLabels()
        }
        .map(XcfaLabel::toStmt)

    val unfoldResult =
      StmtUtils.toExpr(SequenceStmt.of(stmts), VarIndexingFactory.basicVarIndexing(0))
    val expr = PathUtils.unfold(And(unfoldResult.exprs), VarIndexingFactory.indexing(0))
    // var[0] is oldParam, var[-1]is newParam, everything else is a fresh param
    var cnt = 0
    val consts =
      ExprUtils.getIndexedConstants(expr).associateWith {
        if (it.index == 0) oldParams[it.varDecl]!!
        else if (it.index == unfoldResult.indexing[it.varDecl]) newParams[it.varDecl]!!
        else Param("__tmp_${cnt++}", it.type)
      }
    val newParamList =
      vars
        .map {
          if (unfoldResult.indexing[it] == 0 && it != rankingFunction) oldParams[it]!!.ref
          else newParams[it]!!.ref
        }
        .toTypedArray()
    val paramdExpr = ExprUtils.changeDecls(expr, consts)
    (ufs[it.target]!!)(*newParamList) +=
      (ufs[it.source]!!)(*oldParamList).expr +
        paramdExpr +
        rankingFuncConstr.constraint(
          oldParams[rankingFunction]!!.ref as Expr<IntType>,
          newParams[rankingFunction]!!.ref as Expr<IntType>,
        )
  }

  if (termination) {
    ufs
      .filter { !it.key.initial }
      .map { it.value }
      .forEach {
        !(it(*oldParamList) with
          And(
            it(
                oldParamList
                  .map {
                    if (it.decl == oldParams[rankingFunction]) {
                      newParams[rankingFunction]!!.ref
                    } else {
                      it
                    }
                  }
                  .toList()
              )
              .expr,
            Neq(oldParams[rankingFunction]!!.ref, newParams[rankingFunction]!!.ref),
          ))
      }
  } else if (errorLoc.isPresent) {
    !(ufs[errorLoc.get()]!!(*oldParamList))
  }

  ufs[initLoc]!!(*oldParamList) += True()

  return Pair(vars, ufs.values.toList())
}

fun XcfaProcedure.toSMT2CHC(
  termination: Boolean = false,
  rankingFunction: RankingFunction,
): String {
  val chc = toCHC(termination, rankingFunction).second
  val smt2 = chc.toSMT2()
  return smt2
}

fun List<Relation>.toSMT2(): String {
  val symbolTable = GenericSmtLibSymbolTable()
  val transformationManager = GenericSmtLibTransformationManager(symbolTable)
  val terms = flatMap {
    it.rules.map { "(assert " + transformationManager.toTerm(it.toExpr()) + ")" }
  }
  val decls =
    filter { symbolTable.definesConst(it.constDecl) }
      .map { symbolTable.getDeclaration(it.constDecl) }

  return """
; generated by Theta
; https://github.com/ftsrg/theta/

(set-logic HORN)

; declarations
${decls.joinToString("\n")}

; facts, rules, queries
${terms.joinToString("\n")}

(check-sat)
(exit)
"""
    .trimIndent()
}

fun Relation.toSMT2() = listOf(this).toSMT2()
