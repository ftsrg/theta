/*
 *  Copyright 2024-2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.oc

import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverStatus

class IDLOcChecker<E : Event> : OcChecker<E> {
  private var isSc: Boolean = false

  override val solver: Solver = SolverManager.resolveSolverFactory("Z3:4.13").createSolver()

  private var clkGlobalCnt = 0
  private val clkGlobalVars: MutableMap<Int, ConstDecl<IntType>> = mutableMapOf()
  private val Int.clkGlobalVar: ConstDecl<IntType>
    get() = clkGlobalVars.getOrPut(this) { Decls.Const("__clk_global__${clkGlobalCnt++}", Int()) }

  private var clkAtomicCnt = 0
  private val clkAtomicVars: MutableMap<E, ConstDecl<IntType>> = mutableMapOf()
  private val E.clkAtomicVar: ConstDecl<IntType>
    get() = clkAtomicVars.getOrPut(this) { Decls.Const("__clk_atomic__${clkAtomicCnt++}", Int()) }

  private lateinit var hbVars: Array<Array<ConstDecl<BoolType>?>> // happens-before variables

  private lateinit var events: List<E>

  private fun hbVar(i: Int, j: Int): Expr<BoolType> {
    check(i != j)
    if (isSc) return Lt(i.clkGlobalVar.ref, j.clkGlobalVar.ref)
    return hbVars[i][j]?.ref
      ?: Decls.Const("__hb__${i}_${j}", Bool())
        .also {
          hbVars[i][j] = it
          addLt(it.ref, i, j)
        }
        .ref
  }

  private fun addImpl(cond: Expr<BoolType>?, expr: Expr<BoolType>) =
    cond?.let { solver.add(Imply(it, expr)) } ?: solver.add(expr)

  private fun addLt(cond: Expr<BoolType>?, clk1: Int, clk2: Int) {
    check(clk1 != clk2)
    val lt = Lt(clk1.clkGlobalVar.ref, clk2.clkGlobalVar.ref)
    addImpl(cond, lt)
  }

  private fun addLt(cond: Expr<BoolType>?, e1: E, e2: E) {
    if (e1.clkId == e2.clkId) {
      addImpl(cond, Lt(e1.clkAtomicVar.ref, e2.clkAtomicVar.ref))
    } else {
      addLt(cond, e1.clkId, e2.clkId)
    }
  }

  private fun addHb(cond: Expr<BoolType>?, clk1: Int, clk2: Int) = addImpl(cond, hbVar(clk1, clk2))

  private fun addHb(cond: Expr<BoolType>?, e1: E, e2: E) {
    if (isSc || e1.clkId == e2.clkId) return addLt(cond, e1, e2)
    addHb(cond, e1.clkId, e2.clkId)
  }

  private fun addNeq(clkVars: Collection<ConstDecl<IntType>>) {
    clkVars.forEach { v1 ->
      clkVars.forEach { v2 ->
        if (v1 != v2) {
          solver.add(Neq(v1.ref, v2.ref))
        }
      }
    }
  }

  override fun check(
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    pos: List<Relation<E>>,
    ppos: Array<Array<Boolean>>,
    rfs: Map<VarDecl<*>, Set<Relation<E>>>,
    wss: Map<VarDecl<*>, Set<Relation<E>>>,
    isSc: Boolean,
  ): SolverStatus? {
    this.isSc = isSc
    this.events = events.values.flatMap { it.values }.flatten()
    hbVars = Array(Event.clkIdSize) { arrayOfNulls(Event.clkIdSize) }

    // PPO
    ppos.forEachIndexed { i, row ->
      row.forEachIndexed { j, enabled ->
        if (enabled) {
          addHb(null, i, j)
        }
      }
    }
    pos.forEach {
      if (it.from.clkId == it.to.clkId) {
        addHb(null, it.from, it.to)
      }
    }

    // RF
    rfs.forEach { (_, vRfs) -> vRfs.forEach { addHb(it.declRef, it.from, it.to) } }

    // WS
    wss.forEach { (_, vWss) ->
      val wsList = vWss.toList()
      for ((index, ws1) in wsList.withIndex()) {
        addHb(ws1.declRef, ws1.from, ws1.to)
        for (ws2 in wsList.subList(index + 1, wsList.size)) {
          if (ws1.from == ws2.to && ws1.to == ws2.from) {
            addWsCond(solver, ws1, ws2)
          }
        }
      }
    }

    // FR
    rfs.forEach { (v, vRfs) ->
      val writes = events[v]?.values?.flatten()?.filter { it.type == EventType.WRITE }
      writes?.forEach { w1 ->
        writes.forEach { w2 ->
          if (w1 != w2) {
            vRfs.forEach { rf ->
              if (w1 == rf.from) {
                val wsExpr =
                  And(
                    w1.guardExpr,
                    w2.guardExpr,
                    if (w1.clkId == w2.clkId) {
                      Lt(w1.clkAtomicVar.ref, w2.clkAtomicVar.ref)
                    } else {
                      hbVar(w1.clkId, w2.clkId)
                    },
                  )
                addHb(And(wsExpr, rf.declRef), rf.to, w2)
              }
            }
          }
        }
      }
    }

    // Transitivity
    if (!isSc) {
      for (i in 0 until Event.clkIdSize) {
        for (j in 0 until Event.clkIdSize) {
          if (i == j) continue
          val hbIJ = hbVar(i, j)
          for (k in 0 until Event.clkIdSize) {
            if (i == k || j == k) continue
            val hbJK = hbVar(j, k)
            val hbIK = hbVar(i, k)
            addImpl(And(hbIJ, hbJK), hbIK)
          }
        }
      }
    }

    addNeq(clkGlobalVars.values)
    addNeq(clkAtomicVars.values)

    return solver.check()
  }

  override fun getRelations(): Array<Array<Reason?>> {
    val model = solver.model.toMap()
    val rels = Array(Event.clkIdSize) { Array<Reason?>(Event.clkIdSize) { null } }
    events.forEach { e1 ->
      events.forEach { e2 ->
        if (e1.clkId != e2.clkId) {
          if (isSc) {
            val clk1 = model[e1.clkId.clkGlobalVar] as IntLitExpr
            val clk2 = model[e2.clkId.clkGlobalVar] as IntLitExpr
            if (clk1.value < clk2.value) {
              rels[e1.clkId][e2.clkId] = UndetailedReason
            } else {
              check(clk1.value > clk2.value)
              check(rels[e1.clkId][e2.clkId] == null)
            }
          } else {
            val hb = model[hbVars[e1.clkId][e2.clkId]] as BoolLitExpr
            if (hb.value) {
              rels[e1.clkId][e2.clkId] = UndetailedReason
            } else {
              check(rels[e1.clkId][e2.clkId] == null)
            }
          }
        }
      }
    }
    return rels
  }

  override fun getPropagatedClauses(): List<Reason> = emptyList()
}
