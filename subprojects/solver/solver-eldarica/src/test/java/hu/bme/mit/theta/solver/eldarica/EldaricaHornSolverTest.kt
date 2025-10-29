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

import hu.bme.mit.theta.core.ParamHolder
import hu.bme.mit.theta.core.Relation
import hu.bme.mit.theta.core.decl.Decls.Const
import hu.bme.mit.theta.core.plus
import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvSDivExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.bvtype.BvURemExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import java.math.BigInteger
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

class EldaricaHornSolverTest {

  companion object {
    val symbolTable = EldaricaSymbolTable()
    val transformationManager = EldaricaTransformationManager(symbolTable)
    val termTransformer = EldaricaTermTransformer(symbolTable)
    val hornSolver = EldaricaHornSolver(transformationManager, termTransformer)
    val helperSolver = Z3SolverFactory.getInstance().createSolver()
  }

  @BeforeEach
  fun before() {
    hornSolver.push()
  }

  @AfterEach
  fun after() {
    hornSolver.pop()
  }

  @Test
  fun testSolvable() {
    val p = ParamHolder(Int())
    val init = Relation("init", Int(), Int())
    val inv = Relation("inv", Int(), Int())

    init(p[0], p[1]) += Eq(p[0], Int(0)) + Eq(p[1], Int(1))
    inv(p[0], p[1]) += init(p[0], p[1]).expr
    inv(p[0], p[2]) += inv(p[0], p[1]).expr + Eq(p[2], Add(p[1], Int(1)))

    !(inv(p[0], p[1]) with Lt(p[1], Int(1)))

    hornSolver.add(init)
    hornSolver.add(inv)

    val status = hornSolver.check()
    Assertions.assertTrue(status.isSat)
    val model = hornSolver.model.toMap()

    for ((decl, expr) in model.entries) {
      System.err.println("$decl: $expr")
    }

    Assertions.assertTrue(model.containsKey(inv.constDecl))
    Assertions.assertTrue(model.containsKey(init.constDecl))
  }

  @Test
  fun testSolvableBv() {
    val type = BvType.of(32)
    val two = BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.TWO, 32)
    val one = BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ONE, 32)
    val zero = BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, 32)

    val p = ParamHolder(type)
    val init = Relation("init", type, type)
    val inv = Relation("inv", type, type)

    init(p[0], p[1]) += Eq(p[0], zero) + Eq(BvSDivExpr.create(p[1], two), one)
    inv(p[0], p[2]) += init(p[0], p[1]).expr + Eq(p[2], Add(p[1], one))

    !(inv(p[0], p[1]) with Eq(p[1], two))

    hornSolver.add(init)
    hornSolver.add(inv)

    val status = hornSolver.check()
    Assertions.assertTrue(status.isSat)
    val model = hornSolver.model.toMap()

    for ((decl, expr) in model.entries) {
      System.err.println("$decl: $expr")
    }

    Assertions.assertTrue(model.containsKey(inv.constDecl))
    Assertions.assertTrue(model.containsKey(init.constDecl))
  }

  @Test
  fun testUnsolvable() {
    val p = ParamHolder(Int())
    val init = Relation("init", Int(), Int())
    val inv = Relation("inv", Int(), Int())

    init(p[0], p[1]) += Eq(p[0], Int(0)) + Eq(p[1], Int(1))
    inv(p[0], p[1]) += init(p[0], p[1]).expr
    inv(p[0], p[2]) += inv(p[0], p[1]).expr + Eq(p[2], Add(p[1], Int(1)))

    !(inv(p[0], p[1]) with Leq(p[1], Int(1)))

    hornSolver.add(init)
    hornSolver.add(inv)

    val status = hornSolver.check()
    Assertions.assertTrue(status.isUnsat)

    val proof = hornSolver.proof
    System.err.println(proof.toString())
    Assertions.assertTrue(proof != null)
  }

  @Test
  fun testNonlinearUnsolvable() {
    val p = ParamHolder(Int())
    val init1 = Relation("init1", Int(), Int())
    val init2 = Relation("init2", Int(), Int())
    val inv1 = Relation("inv1", Int(), Int())
    val inv2 = Relation("inv2", Int(), Int())

    val err = Relation("err", Int(), Int())

    init1(p[0], p[1]) += Eq(p[0], Int(0)) + Eq(p[1], Int(0))
    init2(p[0], p[1]) += Eq(p[0], Int(0)) + Eq(p[1], Int(0))
    inv1(p[0], p[1]) += init1(p[0], p[1]).expr
    inv1(p[0], p[2]) += inv1(p[0], p[1]).expr + Eq(p[2], Add(p[1], Int(3)))
    inv2(p[0], p[1]) += init2(p[0], p[1]).expr
    inv2(p[0], p[2]) += inv2(p[0], p[1]).expr + Eq(p[2], Add(p[1], Int(5)))

    err(p[0], p[2]) += inv1(p[0], p[1]).expr + inv2(p[0], p[1]).expr + Gt(p[1], Int(0))

    !err(p[0], p[1])

    hornSolver.add(init1)
    hornSolver.add(init2)
    hornSolver.add(inv1)
    hornSolver.add(inv2)
    hornSolver.add(err)

    val status = hornSolver.check()
    Assertions.assertTrue(status.isUnsat)

    val proof = hornSolver.proof
    System.err.println(proof.toString())
    Assertions.assertTrue(proof != null)
  }

  @Test
  fun testInterpolationInt() {
    val x = Const("x", Int())
    val y = Const("y", Int())
    val z = Const("z", Int())
    val tasks =
      listOf(
        Pair(And(Eq(x.ref, y.ref), Eq(y.ref, z.ref)), Neq(x.ref, z.ref)),
        Pair(Eq(Add(x.ref, Int(2)), y.ref), Lt(y.ref, x.ref)),
      )

    testItp(tasks)
  }

  @Test
  fun testInterpolationBv() {
    val x = Const("x", BvType.of(32))
    val y = Const("y", BvType.of(32))
    val z = Const("z", BvType.of(32))

    val one = BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ONE, 32)
    val two = BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.TWO, 32)

    val tasks =
      listOf(
        Pair(And(Eq(x.ref, y.ref), Eq(y.ref, z.ref)), Neq(x.ref, z.ref)),
        Pair(
          And(Eq(Add(x.ref, two), y.ref), Eq(Sub(y.ref, x.ref), z.ref)),
          Eq(BvURemExpr.create(z.ref, two), one),
        ),
      )

    testItp(tasks)
  }

  private fun testItp(tasks: List<Pair<Expr<BoolType>, BinaryExpr<out Type, BoolType>>>) {
    for ((a, b) in tasks) {
      hornSolver.push()
      val itp = hornSolver.interpolate(a, b)
      System.err.println("itp($a, $b)\n\t= $itp")
      val consts = ExprUtils.getConstants(itp)
      val allowedConsts = ExprUtils.getConstants(a) intersect ExprUtils.getConstants(b)
      Assertions.assertTrue { allowedConsts.containsAll(consts) }
      WithPushPop(helperSolver).use {
        helperSolver.add(Not(Imply(a, itp)))
        Assertions.assertTrue { helperSolver.check().isUnsat }
      }
      WithPushPop(helperSolver).use {
        helperSolver.add(And(b, itp))
        Assertions.assertTrue { helperSolver.check().isUnsat }
      }
      hornSolver.pop()
    }
  }
}
