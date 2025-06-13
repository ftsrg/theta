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
package hu.bme.mit.theta.solver.eldarica

import ap.parser.IAtom
import ap.parser.IBoolLit
import ap.parser.IExpression
import ap.parser.IExpression.and
import ap.parser.IFormula
import com.google.common.base.Preconditions
import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.core.Relation
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decls.Const
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.ForallExpr
import hu.bme.mit.theta.core.type.functype.FuncLitExpr
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.HornSolver
import hu.bme.mit.theta.solver.ProofNode
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.eldarica.Utils.*
import hu.bme.mit.theta.solver.impl.StackImpl
import lazabs.horn.Util
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.`HornClauses$`
import scala.Tuple2

class EldaricaHornSolver(
  val manager: EldaricaTransformationManager,
  val termTransformer: EldaricaTermTransformer,
) : HornSolver {
  private val clauses = StackImpl<HornClauses.Clause>()

  private var status: SolverStatus? = null
  private var model: Valuation? = null
  private var proof: ProofNode? = null

  override fun add(assertion: Expr<BoolType>) {
    throw UnsupportedOperationException("Not supported")
  }

  override fun add(relation: Relation) {
    status = null
    model = null
    proof = null
    for (rule in relation.rules) {
      val paramToConst =
        (rule.toExpr() as ForallExpr).paramDecls.associateWith { Const(it.name, it.type) }
      val head = manager.toTerm(ExprUtils.changeDecls(rule.head, paramToConst)).asExpression()
      val constraints =
        rule.constraints
          .flatMap { ExprUtils.getConjuncts(it) }
          .map { manager.toTerm(ExprUtils.changeDecls(it, paramToConst)).asExpression() }

      val body = constraints.filterIsInstance<IAtom>().toList()

      val cnstr = and(getIterable(constraints.filter { !body.contains(it) }.map { it as IFormula }))

      if (head is IAtom) {
        val clause = HornClauses.Clause(head, getIterable(body).toList(), cnstr)
        clauses.add(clause)
      } else if (head is IBoolLit && !head.value()) {
        val clause =
          HornClauses.Clause(
            IExpression.toPredApplier(`HornClauses$`.`MODULE$`.FALSE()).apply(toSeq(emptyList())),
            getIterable(body).toList(),
            cnstr,
          )
        clauses.add(clause)
      }
    }
  }

  override fun check(): SolverStatus {
    val answer = check(clauses.toCollection())
    if (answer.isLeft) {
      val model = answer.left().get()
      status = SolverStatus.SAT
      this.model =
        ImmutableValuation.from(
          toMap(model)
            .mapNotNull { (pred, formula) ->
              val decl = termTransformer.toDecl(pred) as ConstDecl<FuncType<*, *>>
              val params = extractParamTypes(decl.type).first.mapIndexed { i, t -> Param("P$i", t) }
              var expr = termTransformer.toExpr(formula, params)
              for (paramDecl in params) {
                expr = FuncLitExpr.of(paramDecl, expr)
              }
              Pair(decl, expr as FuncLitExpr<*, *>)
            }
            .toMap()
        )
    } else {
      val dag = answer.right().get()
      status = SolverStatus.UNSAT
      this.proof = transformProof(dag)!!.build()
    }
    return status!!
  }

  fun extractParamTypes(type: Type): Pair<List<Type>, Type> {
    if (type is FuncType<*, *>) {
      val funcType = type

      val paramType: Type = funcType.getParamType()
      val resultType: Type = funcType.getResultType()

      Preconditions.checkArgument(paramType !is FuncType<*, *>)

      val subResult = extractParamTypes(resultType)
      val paramTypes = subResult.first
      val newResultType = subResult.second
      val newParamTypes = ImmutableList.builder<Type>().add(paramType).addAll(paramTypes).build()
      val result = Pair(newParamTypes, newResultType)

      return result
    } else {
      return Pair(ImmutableList.of(), type)
    }
  }

  private fun transformProof(dag: Util.Dag<Tuple2<IAtom, HornClauses.Clause>>): ProofNode.Builder? {
    val nodeList = Array<ProofNode.Builder?>(dag.size()) { null }

    var d = dag
    var i = 0
    while (d is Util.DagNode<Tuple2<IAtom, HornClauses.Clause>>) {
      nodeList[i++] = ProofNode.Builder(termTransformer.toExpr(d.head()._1) as Expr<BoolType>)
      d = d.next()
    }

    d = dag
    i = 0
    while (d is Util.DagNode<Tuple2<IAtom, HornClauses.Clause>>) {
      val proofNode = nodeList[i++]!!
      getIterable(d.children()).forEach { it ->
        val idx = it as Int + i - 1
        if (idx < dag.size()) proofNode.addChild(nodeList[idx])
      }
      d = d.next()
    }
    return nodeList[0]
  }

  override fun push() {
    clauses.push()
  }

  override fun pop(n: Int) {
    clauses.pop(n)
  }

  override fun reset() {
    clauses.clear()
  }

  override fun getStatus(): SolverStatus? = status

  override fun getModel(): Valuation = model!!

  override fun getProof(): ProofNode = proof!!

  override fun getAssertions(): Collection<Expr<BoolType>> {
    throw UnsupportedOperationException("Not supported")
  }

  override fun close() {}
}
