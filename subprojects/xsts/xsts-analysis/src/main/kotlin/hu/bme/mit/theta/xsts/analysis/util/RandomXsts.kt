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
package hu.bme.mit.theta.xsts.analysis.util

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xsts.XSTS
import kotlin.random.Random

@JvmOverloads
fun generateXsts(
  seed: Int,
  numCtrl: Int = 1,
  numClock: Int = 1,
  numOther: Int = 3,
  requireAllVarsWritten: Boolean = false,
): XSTS {
  val writtenVars =
    object : StmtVisitor<Set<VarDecl<*>>, Set<VarDecl<*>>> {
      override fun visit(stmt: SkipStmt?, param: Set<VarDecl<*>>): Set<VarDecl<*>> {
        return param
      }

      override fun visit(stmt: AssumeStmt?, param: Set<VarDecl<*>>): Set<VarDecl<*>> {
        return param
      }

      override fun <DeclType : Type?> visit(
        stmt: AssignStmt<DeclType>,
        param: Set<VarDecl<*>>,
      ): Set<VarDecl<*>> {
        return setOf(stmt.varDecl) + param
      }

      override fun <DeclType : Type?> visit(
        stmt: HavocStmt<DeclType>,
        param: Set<VarDecl<*>>,
      ): Set<VarDecl<*>> {
        return setOf(stmt.varDecl) + param
      }

      override fun visit(stmt: SequenceStmt, param: Set<VarDecl<*>>): Set<VarDecl<*>> {
        var res = param
        for (s in stmt.stmts) {
          res = s.accept(this, setOf())
        }
        return res
      }

      override fun visit(stmt: NonDetStmt, param: Set<VarDecl<*>>): Set<VarDecl<*>> {
        var res = param
        for (s in stmt.stmts) {
          res = s.accept(this, setOf())
        }
        return res
      }

      override fun visit(stmt: OrtStmt?, param: Set<VarDecl<*>>?): Set<VarDecl<*>> {
        TODO("Not yet implemented")
      }

      override fun visit(stmt: LoopStmt, param: Set<VarDecl<*>>): Set<VarDecl<*>> {
        return stmt.stmt.accept(this, param)
      }

      override fun visit(stmt: IfStmt, param: Set<VarDecl<*>>): Set<VarDecl<*>> {
        return stmt.then.accept(this, stmt.elze.accept(this, param))
      }

      override fun <PtrType : Type?, OffsetType : Type?, DeclType : Type?> visit(
        stmt: MemoryAssignStmt<PtrType, OffsetType, DeclType>?,
        param: Set<VarDecl<*>>?,
      ): Set<VarDecl<*>> {
        TODO("Not yet implemented")
      }
    }

  val all = numCtrl + numOther + numClock
  val xsts =
    RandomXsts(seed, 3).generateRandomXsts(10, numCtrl, numClock, numOther) {
      if (requireAllVarsWritten) {
        val decls = it.tran.accept(writtenVars, setOf())
        decls.size == all // all vars are written
      } else {
        true
      }
    }
  return xsts
}

class RandomXsts(seed: Int, val exprMaxDepth: Int) {

  lateinit var ctrlVars: List<VarDecl<IntType>>
  lateinit var otherVars: List<VarDecl<Type>>
  lateinit var boolVars: List<VarDecl<BoolType>>
  lateinit var clockVars: List<VarDecl<IntType>>
  lateinit var intVars: List<VarDecl<IntType>>

  val random = Random(seed)

  fun generateRandomXsts(
    depth: Int,
    numCtrl: Int,
    numClock: Int,
    numOther: Int,
    constraint: (XSTS) -> Boolean,
  ): XSTS {
    var xsts: XSTS
    do {
      val trans = generateRandomStmt(depth, numCtrl, numClock, numOther)
      val env = Stmts.NonDetStmt(listOf(Stmts.Skip()))
      val init = Stmts.NonDetStmt(listOf(Stmts.Skip()))
      val initExpr =
        BoolExprs.And(
          ctrlVars.map { IntExprs.Eq(it.ref, IntExprs.Int(0)) } +
            boolVars.map { BoolExprs.Not(it.ref) } +
            intVars.map { IntExprs.Eq(it.ref, IntExprs.Int(0)) }
        )
      var expr: Expr<BoolType>
      do expr = randomBoolExpr(0) while (ExprUtils.getVars(expr).isEmpty())
      xsts = XSTS(ctrlVars.toSet(), init, NonDetStmt.of(listOf(trans)), env, initExpr, expr)
    } while (!(constraint(xsts)))
    return xsts
  }

  fun generateRandomStmt(depth: Int, numCtrl: Int, numClock: Int, numOther: Int): Stmt {
    var i = 2
    ctrlVars = Array(numCtrl) { Decls.Var("ctlr${i++}", IntType.getInstance()) }.toList()
    do {
      otherVars =
        listOf(
          Decls.Var("var0", IntType.getInstance()) as VarDecl<Type>,
          Decls.Var("var1", BoolType.getInstance()) as VarDecl<Type>,
        ) + Array(numOther - 2) { randomVar("var${i++}") }.toList()
    } while (otherVars.all { it.type is IntType } || otherVars.all { it.type is BoolType })
    boolVars = otherVars.filter { it.type is BoolType }.map { it as VarDecl<BoolType> }
    intVars = otherVars.filter { it.type is IntType }.map { it as VarDecl<IntType> }
    clockVars = Array(numClock) { Decls.Var("clock${i++}", IntType.getInstance()) }.toList()

    return randomIntermediate(0, depth)
  }

  fun randomVar(name: String): VarDecl<Type> {
    return listOf(
        { Decls.Var(name, IntType.getInstance()) as VarDecl<Type> },
        { Decls.Var(name, BoolType.getInstance()) as VarDecl<Type> },
      )
      .random(random)()
  }

  fun randomIntermediate(currDepth: Int, maxDepth: Int): Stmt {
    if (currDepth == maxDepth) return randomLeaf()
    return listOf(
        { randomLeaf() },
        { randomSeq(currDepth + 1, maxDepth) },
        { randomNonDet(currDepth + 1, maxDepth) },
        { randomIf(currDepth + 1, maxDepth) },
        //                { randomLoop(currDepth + 1, maxDepth) },
      )
      .random(random)()
  }

  fun randomLeaf(): Stmt {
    return listOf(
        //            { Stmts.Skip() },
        { randomAssign() },
        { randomAssign() },
        { randomAssume() },
        //                { randomHavoc() },
      )
      .random(random)()
  }

  fun randomSeq(currDepth: Int, maxDepth: Int): Stmt {
    return Stmts.SequenceStmt(
      listOf(
        randomIntermediate(currDepth + 1, maxDepth),
        randomIntermediate(currDepth + 1, maxDepth),
      )
    )
  }

  fun randomNonDet(currDepth: Int, maxDepth: Int): Stmt {
    return Stmts.NonDetStmt(
      listOf(
        randomIntermediate(currDepth + 1, maxDepth),
        randomIntermediate(currDepth + 1, maxDepth),
      )
    )
  }

  fun randomIf(currDepth: Int, maxDepth: Int): Stmt {
    var expr: Expr<BoolType>
    do expr = randomBoolExpr(0) while (ExprUtils.getVars(expr).isEmpty())
    return IfStmt.of(
      expr,
      randomIntermediate(currDepth + 1, maxDepth),
      randomIntermediate(currDepth + 1, maxDepth),
    )
  }

  fun randomBoolExpr(currDepth: Int): Expr<BoolType> {
    return (if (currDepth == exprMaxDepth)
      listOf({ BoolExprs.True() }, { boolVars[random.nextInt((boolVars.size))].ref }).random(random)
    else
      listOf(
          { BoolExprs.True() },
          { boolVars[random.nextInt((boolVars.size))].ref },
          { BoolExprs.Not(randomBoolExpr(currDepth + 1)) },
          { BoolExprs.And(randomBoolExpr(currDepth + 1), randomBoolExpr(currDepth + 1)) },
          { BoolExprs.Or(randomBoolExpr(currDepth + 1), randomBoolExpr(currDepth + 1)) },
          { BoolExprs.Imply(randomBoolExpr(currDepth + 1), randomBoolExpr(currDepth + 1)) },
          { BoolExprs.Iff(randomBoolExpr(currDepth + 1), randomBoolExpr(currDepth + 1)) },
          { BoolExprs.Xor(randomBoolExpr(currDepth + 1), randomBoolExpr(currDepth + 1)) },
          { IntExprs.Eq(randomIntExpr(currDepth + 1), randomIntExpr(currDepth + 1)) },
          { IntExprs.Geq(randomIntExpr(currDepth + 1), randomIntExpr(currDepth + 1)) },
          { IntExprs.Leq(randomIntExpr(currDepth + 1), randomIntExpr(currDepth + 1)) },
          { IntExprs.Lt(randomIntExpr(currDepth + 1), randomIntExpr(currDepth + 1)) },
          { IntExprs.Gt(randomIntExpr(currDepth + 1), randomIntExpr(currDepth + 1)) },
          { IntExprs.Neq(randomIntExpr(currDepth + 1), randomIntExpr(currDepth + 1)) },
        )
        .random(random))()
  }

  fun randomIntExpr(currDepth: Int): Expr<IntType> {
    return (if (currDepth == exprMaxDepth)
      listOf({ IntExprs.Int(random.nextInt(5)) }, { intVars[random.nextInt((intVars.size))].ref })
        .random(random)
    else
      listOf(
          { IntExprs.Int(random.nextInt(5)) },
          { intVars[random.nextInt((intVars.size))].ref },
          { IntExprs.Neg(randomIntExpr(currDepth + 1)) },
          { IntExprs.Add(randomIntExpr(currDepth + 1), randomIntExpr(currDepth + 1)) },
          { IntExprs.Mul(randomIntExpr(currDepth + 1), randomIntExpr(currDepth + 1)) },
          { IntExprs.Sub(randomIntExpr(currDepth + 1), randomIntExpr(currDepth + 1)) },
        )
        .random(random))()
  }

  fun randomLoop(currDepth: Int, maxDepth: Int): Stmt {
    return LoopStmt.of(
      randomIntermediate(currDepth + 1, maxDepth),
      ctrlVars.random(random),
      IntExprs.Int(0),
      randomIntExpr(0) { ctrlVars.containsAll(ExprUtils.getVars(it)) },
    )
  }

  fun randomAssign(): Stmt {
    return (listOf(
        {
          val v = otherVars.random(random)
          when (v.type) {
            is IntType ->
              Stmts.Assign(
                v as VarDecl<IntType>,
                randomIntExpr { ExprUtils.getVars(it).size > 0 && it != v.ref },
              )

            is BoolType ->
              Stmts.Assign(
                v as VarDecl<BoolType>,
                randomBoolExpr { ExprUtils.getVars(it).size > 0 && it != v.ref },
              )

            else -> throw Exception()
          }
        },
        { Stmts.Assign(ctrlVars.random(random), randomIntExpr(0)) },
      ) + (if (clockVars.isEmpty()) listOf() else listOf({ randomClockReset() })))
      .random(random)()
  }

  fun randomIntExpr(currDepth: Int = 0, constraint: (Expr<IntType>) -> Boolean): Expr<IntType> {
    var res: Expr<IntType>
    do {
      res = randomIntExpr(currDepth)
    } while (!(constraint(res)))
    return res
  }

  fun randomBoolExpr(currDepth: Int = 0, constraint: (Expr<BoolType>) -> Boolean): Expr<BoolType> {
    var res: Expr<BoolType>
    do {
      res = randomBoolExpr(currDepth)
    } while (!(constraint(res)))
    return res
  }

  fun randomAssume() =
    (listOf(this::randomDataAssume) +
        (if (clockVars.isEmpty()) listOf() else listOf(this::randomClockConstraint)))
      .random(random)()

  fun randomDataAssume(): Stmt {
    var expr: Expr<BoolType>
    do expr = randomBoolExpr(0) while (ExprUtils.getVars(expr).isEmpty())

    return Stmts.Assume(expr)
  }

  fun randomClockReset(): Stmt {
    val c = clockVars.random(random)
    val resetTo = IntExprs.Int(random.nextInt(4))
    return Stmts.Assign(c, resetTo)
  }

  fun randomClockConstraint(): Stmt {
    val c =
      if (clockVars.size == 1) clockVars[0].ref
      else
        listOf(
            { clockVars.random(random).ref },
            {
              val c1 = clockVars.random(random)
              val c2 = (clockVars - listOf(c1)).random()
              IntExprs.Sub(c1.ref, c2.ref)
            },
          )
          .random()()

    val compareTo = IntExprs.Int(random.nextInt(10))
    return Stmts.Assume(
      listOf(
          { IntExprs.Leq(c, compareTo) },
          { IntExprs.Lt(c, compareTo) },
          { IntExprs.Geq(c, compareTo) },
          { IntExprs.Gt(c, compareTo) },
          { IntExprs.Eq(c, compareTo) },
        )
        .random(random)()
    )
  }

  fun randomHavoc(): Stmt {
    return Stmts.Havoc((otherVars + clockVars).random(random))
  }
}
