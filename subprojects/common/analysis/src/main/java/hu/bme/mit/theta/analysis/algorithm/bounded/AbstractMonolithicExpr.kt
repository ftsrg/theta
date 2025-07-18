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

import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.*
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import java.util.HashMap

fun MonolithicExpr.createAbstract(prec: PredPrec): MonolithicExpr {
  // TODO: handle initOffsetIndex in abstract initExpr
  val lambdaList = ArrayList<IffExpr>()
  val lambdaPrimeList = ArrayList<IffExpr>()
  val activationLiterals = ArrayList<VarDecl<*>>()
  val literalToPred = HashMap<Decl<*>, Expr<BoolType>>()

  prec.preds.forEachIndexed { index, expr ->
    run {
      val v = Decls.Var("v$index", BoolType.getInstance())
      activationLiterals.add(v)
      literalToPred[v] = expr
      lambdaList.add(IffExpr.of(v.ref, expr))
      lambdaPrimeList.add(
        BoolExprs.Iff(Exprs.Prime(v.ref), ExprUtils.applyPrimes(expr, this.transOffsetIndex))
      )
    }
  }

  /*
  The idea for a transition is that activation literals are equal the initial value of their predicate, and are
  assigned the final value of their predicate after the transition. However, the indices of ordinary variables are
  incremented by 1 more than necessary, thus two transitions after each other are 'connected' only via activation
  literals, and not by others (ctrlVars are exempt from this).

  for example, if there is a transition {a:1 == a:0 + 1, a:2 := b:0 + a:1} with an offsetindex {a: 2, b: 0}, with
  a predicate {a == b} for activation literal v0, then the new transition is
  {v0:0 == (a:0 == b:0), a:1 == a:0 + 1, a:2 := b:0 + a:1, v0:1 == (a:2 == b:0)} with offsetindex {a: 3, b: 1, v0: 1}
  ~~~~~~~~^ init act. literal
  ~~~~~~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^ original trans
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^ updated act. literal
   */

  var indexingBuilder = VarIndexingFactory.indexingBuilder(1)
  this.vars
    .filter { it !in ctrlVars }
    .forEach { decl ->
      repeat(transOffsetIndex.get(decl)) { indexingBuilder = indexingBuilder.inc(decl) }
    }
  ctrlVars.forEach { decl ->
    // -1, because ctrlVars have to keep their initial index
    repeat(transOffsetIndex.get(decl) - 1) { indexingBuilder = indexingBuilder.inc(decl) }
    // the special case where its original index is 0
    if (transOffsetIndex.get(decl) == 0) {
      indexingBuilder = indexingBuilder.dec(decl)
    }
  }

  val transExpr = Or(this.split().map { And(lambdaList + lambdaPrimeList + it) })

  return MonolithicExpr(
    initExpr = And(And(lambdaList), initExpr),
    transExpr = transExpr,
    propExpr = Not(And(And(lambdaList), Not(propExpr))),
    transOffsetIndex = indexingBuilder.build(),
    initOffsetIndex = VarIndexingFactory.indexing(0),
    vars = activationLiterals + ctrlVars,
    valToState = { valuation: Valuation ->
      PredState.of(
        valuation
          .toMap()
          .entries
          .stream()
          .filter { /*it.key in vars &&*/
            it.key !in ctrlVars
          }
          .map {
            when ((it.value as BoolLitExpr).value) {
              true -> literalToPred[it.key]
              false -> Not(literalToPred[it.key]!!)
            }
          }
          .toList()
      )
    },
    biValToAction = { _, _ -> this.action() },
    ctrlVars = ctrlVars,
  )
}
