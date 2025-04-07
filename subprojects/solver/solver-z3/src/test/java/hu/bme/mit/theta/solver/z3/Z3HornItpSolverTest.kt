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
package hu.bme.mit.theta.solver.z3

import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.functype.FuncExprs
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.HornItpSolver
import hu.bme.mit.theta.solver.SolverStatus
import org.junit.Assert
import org.junit.Before
import org.junit.Test

class Z3ItpSolverTest {

  var solver: HornItpSolver? = null

  var a: Expr<IntType>? = null
  var b: Expr<IntType>? = null
  var c: Expr<IntType>? = null
  var d: Expr<IntType>? = null
  var e: Expr<IntType>? = null
  var f: Expr<FuncType<IntType, IntType>>? = null
  var g: Expr<FuncType<IntType, IntType>>? = null

  @Before
  fun initialize() {
    solver = Z3SolverFactory.getInstance().createHornItpSolver()

    val ad = Decls.Const("a", IntExprs.Int())
    val bd = Decls.Const("b", IntExprs.Int())
    val cd = Decls.Const("c", IntExprs.Int())
    val dd = Decls.Const("d", IntExprs.Int())
    val ed = Decls.Const("e", IntExprs.Int())
    val fd = Decls.Const("f", FuncExprs.Func(IntExprs.Int(), IntExprs.Int()))
    val gd = Decls.Const("g", FuncExprs.Func(IntExprs.Int(), IntExprs.Int()))

    a = ad.ref
    b = bd.ref
    c = cd.ref
    d = dd.ref
    e = ed.ref
    f = fd.ref
    g = gd.ref
  }

  @Test
  fun testBinaryInterpolation() {
    val A = solver!!.createMarker()
    val B = solver!!.createMarker()
    val pattern = solver!!.createBinPattern(A, B)

    solver!!.add(A, IntExprs.Eq(a, b))
    solver!!.add(A, IntExprs.Eq(a, c))
    solver!!.add(B, IntExprs.Eq(b, d))
    solver!!.add(B, IntExprs.Neq(c, d))

    solver!!.check()
    Assert.assertEquals(SolverStatus.UNSAT, solver!!.status)
    val itp = solver!!.getInterpolant(pattern)

    println(itp.eval(A))
    println("----------")
    Assert.assertTrue(ExprUtils.getVars(itp.eval(A)).size <= 3)
  }

  @Test
  fun testEUF() {
    val A = solver!!.createMarker()
    val B = solver!!.createMarker()
    val pattern = solver!!.createBinPattern(A, B)

    solver!!.add(A, IntExprs.Eq(FuncExprs.App(f, a), c))
    solver!!.add(A, IntExprs.Eq(FuncExprs.App(f, b), d))
    solver!!.add(B, IntExprs.Eq(a, b))
    solver!!.add(B, IntExprs.Neq(FuncExprs.App(g, c), FuncExprs.App(g, d)))

    solver!!.check()
    Assert.assertEquals(SolverStatus.UNSAT, solver!!.status)
    val itp = solver!!.getInterpolant(pattern)

    println(itp.eval(A))
    println("----------")
  }

  @Test
  fun testLIA() {
    val A = solver!!.createMarker()
    val B = solver!!.createMarker()
    val pattern = solver!!.createBinPattern(A, B)

    solver!!.add(A, IntExprs.Eq(b, IntExprs.Mul(ImmutableList.of(IntExprs.Int(2), a!!))))
    solver!!.add(
      B,
      IntExprs.Eq(
        b,
        IntExprs.Add(
          ImmutableList.of(IntExprs.Mul(ImmutableList.of(IntExprs.Int(2), c!!)), IntExprs.Int(1))
        ),
      ),
    )

    solver!!.check()
    Assert.assertEquals(SolverStatus.UNSAT, solver!!.status)
    val itp = solver!!.getInterpolant(pattern)

    println(itp.eval(A))
    println("----------")
  }

  // @Test
  fun testQuantifiers() {
    val A = solver!!.createMarker()
    val B = solver!!.createMarker()
    val pattern = solver!!.createBinPattern(A, B)

    val id = Decls.Const("i", IntExprs.Int())
    val pd = Decls.Const("p", FuncExprs.Func(IntExprs.Int(), BoolExprs.Bool()))
    val qd = Decls.Const("q", FuncExprs.Func(IntExprs.Int(), BoolExprs.Bool()))
    val x1d = Decls.Param("x", IntExprs.Int())
    val x2d = Decls.Param("x", IntExprs.Int())

    val i: Expr<IntType> = id.ref
    val p: Expr<FuncType<IntType, BoolType>> = pd.ref
    val q: Expr<FuncType<IntType, BoolType>> = qd.ref
    val x1: Expr<IntType> = x1d.ref
    val x2: Expr<IntType> = x2d.ref

    solver!!.add(
      A,
      BoolExprs.Forall(
        ImmutableList.of(x1d),
        BoolExprs.Imply(FuncExprs.App(q, x1), FuncExprs.App(p, x1)),
      ),
    )
    solver!!.add(A, BoolExprs.Forall(ImmutableList.of(x2d), BoolExprs.Not(FuncExprs.App(p, x2))))
    solver!!.add(B, FuncExprs.App(q, i))

    solver!!.check()
    Assert.assertEquals(SolverStatus.UNSAT, solver!!.status)
    val itp = solver!!.getInterpolant(pattern)

    println(itp.eval(A))
    println("----------")
  }

  @Test
  fun testPushPop() {
    val A = solver!!.createMarker()
    val B = solver!!.createMarker()
    val pattern = solver!!.createBinPattern(A, B)

    solver!!.add(A, IntExprs.Eq(a, b))
    solver!!.add(B, IntExprs.Eq(b, c))

    solver!!.push()

    solver!!.add(A, IntExprs.Neq(a, c))
    solver!!.check()
    Assert.assertEquals(SolverStatus.UNSAT, solver!!.status)

    solver!!.pop()

    solver!!.add(B, IntExprs.Neq(a, c))
    solver!!.check()
    Assert.assertEquals(SolverStatus.UNSAT, solver!!.status)
    val itp = solver!!.getInterpolant(pattern)

    println(itp.eval(A))
    println("----------")
  }
}
