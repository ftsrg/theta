/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.solver.AssumingSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverStatus

private const val CHUNK_SIZE = 4096

class IDLOcChecker<E : Event>(solverFactory: SolverFactory, private val isSc: Boolean = false) :
  OcChecker<E>() {
  override val solver: Solver = solverFactory.createSolver()

  private var clkGlobalCnt = 0
  private val clkGlobalVars: MutableMap<Int, ConstDecl<IntType>> = mutableMapOf()
  private val Int.clkGlobalVar: ConstDecl<IntType>
    get() =
      clkGlobalVars.getOrPut(this) {
        check(!prepared) { "A clock declared after the encoding misses its disequalities" }
        Decls.Const("__clk_global__${clkGlobalCnt++}", Int())
      }

  private var clkAtomicCnt = 0
  private val clkAtomicVars: MutableMap<E, ConstDecl<IntType>> = mutableMapOf()
  private val E.clkAtomicVar: ConstDecl<IntType>
    get() =
      clkAtomicVars.getOrPut(this) {
        check(!prepared) { "A clock declared after the encoding misses its disequalities" }
        Decls.Const("__clk_atomic__${clkAtomicCnt++}", Int())
      }

  private var prepared = false

  /**
   * Whether all clocks are asserted to differ. A refutation holds without that, so it is added only
   * for a race condition, which compares neighbouring clock values, or to make a model an
   * execution.
   */
  private var allDistinct = false

  private lateinit var hbVars: Array<Array<ConstDecl<BoolType>?>> // happens-before variables

  // kept across checks: a solver refuses a second declaration of the same name
  private val hbDecls: MutableMap<Pair<Int, Int>, ConstDecl<BoolType>> = mutableMapOf()

  private lateinit var events: List<E>

  private fun hbVar(i: Int, j: Int): Expr<BoolType> {
    check(i != j)
    if (isSc) return Lt(i.clkGlobalVar.ref, j.clkGlobalVar.ref)
    return hbVars[i][j]?.ref
      ?: hbDecls
        .getOrPut(i to j) { Decls.Const("__hb__${i}_${j}", Bool()) }
        .also {
          hbVars[i][j] = it
          addLt(it.ref, i, j)
        }
        .ref
  }

  /** Whether the atomic units of [e1] and [e2] are at neighbouring clock values. */
  override fun raceCondition(e1: E, e2: E): Expr<BoolType> {
    check(isSc && e1.clkId != e2.clkId)
    if (!allDistinct) {
      allDistinct = true
      if (prepared) {
        addNeq(clkGlobalVars.values)
        flush()
      }
    }
    val clk1 = e1.clkId.clkGlobalVar.ref
    val clk2 = e2.clkId.clkGlobalVar.ref
    return Or(Eq(Inc(clk1), clk2), Eq(Inc(clk2), clk1))
  }

  // asserted in chunks: a solver call per ordering constraint dominates the encoding time
  private val pending = mutableListOf<Expr<BoolType>>()

  private fun assert(expr: Expr<BoolType>) {
    pending.add(expr)
    if (pending.size >= CHUNK_SIZE) flush()
  }

  private fun flush() {
    if (pending.isEmpty()) return
    solver.add(if (pending.size == 1) pending.first() else And(pending.toList()))
    pending.clear()
  }

  private fun addImpl(cond: Expr<BoolType>?, expr: Expr<BoolType>) =
    assert(cond?.let { Imply(it, expr) } ?: expr)

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
    val vars = clkVars.toList()
    for ((index, v1) in vars.withIndex()) {
      for (v2 in vars.subList(index + 1, vars.size)) assert(Neq(v1.ref, v2.ref))
    }
  }

  override fun check(
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    pos: List<Relation<E>>,
    ppos: BooleanGlobalRelation,
    rfs: Map<VarDecl<*>, Set<Relation<E>>>,
    wss: Map<VarDecl<*>, Set<Relation<E>>>,
  ): SolverStatus? {
    if (!prepared) encode(events, pos, ppos, rfs, wss)
    return assumption?.let { (solver as AssumingSolver).checkAssuming(it) } ?: solver.check()
  }

  override fun prepare(
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    pos: List<Relation<E>>,
    ppos: BooleanGlobalRelation,
    rfs: Map<VarDecl<*>, Set<Relation<E>>>,
    wss: Map<VarDecl<*>, Set<Relation<E>>>,
  ): Boolean {
    encode(events, pos, ppos, rfs, wss)
    prepared = true
    return true
  }

  private fun encode(
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    pos: List<Relation<E>>,
    ppos: BooleanGlobalRelation,
    rfs: Map<VarDecl<*>, Set<Relation<E>>>,
    wss: Map<VarDecl<*>, Set<Relation<E>>>,
  ) {
    this.events = events.values.flatMap { it.values }.flatten()
    hbVars = Array(Event.clkSize) { arrayOfNulls(Event.clkSize) }

    // PPO
    ppos.forEachPair { i, j, enabled ->
      if (enabled) {
        addHb(null, i, j)
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
            addWsCond(ws1, ws2)
          }
        }
      }
    }

    // FR
    rfs.forEach { (v, vRfs) ->
      val writes = events[v]?.values?.flatten()?.filter { it.type == EventType.WRITE }
      val rfsFrom = vRfs.groupBy { it.from }
      writes?.forEach { w1 ->
        writes.forEach { w2 ->
          // a read from w1 is of the cell of w1, which w2 may never write; w2 before w1 is no ws
          if (
            w1 != w2 &&
              w1.potentialSameMemory(w2) &&
              (w1.clkId == w2.clkId || !ppos[w2.clkId, w1.clkId])
          ) {
            rfsFrom[w1]?.forEach { rf ->
              val r = rf.to
              // nothing to enforce when the read is before w2 anyway
              if (r.potentialSameMemory(w2) && (r.clkId == w2.clkId || !ppos[r.clkId, w2.clkId])) {
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
                val sameCell = rf.to.interferenceCond(w2)
                addHb(listOfNotNull(wsExpr, rf.declRef, sameCell).toAnd(), rf.to, w2)
              }
            }
          }
        }
      }
    }

    // Transitivity
    if (!isSc) {
      for (i in 0 until Event.clkSize) {
        for (j in 0 until Event.clkSize) {
          if (i == j) continue
          val hbIJ = hbVar(i, j)
          for (k in 0 until Event.clkSize) {
            if (i == k || j == k) continue
            val hbJK = hbVar(j, k)
            val hbIK = hbVar(i, k)
            addImpl(And(hbIJ, hbJK), hbIK)
          }
        }
      }
    }

    if (allDistinct) addNeq(clkGlobalVars.values)
    addNeq(clkAtomicVars.values)
    flush()
  }

  override fun distinctModel(): SolverStatus? {
    while (!allDistinct) {
      val model = solver.model.toMap()
      val clocks = clkGlobalVars.values
      if (clocks.any { it !in model }) {
        allDistinct = true
        addNeq(clocks)
      } else {
        val tied = clocks.groupBy { model[it] }.values.filter { it.size > 1 }
        if (tied.isEmpty()) return SolverStatus.SAT
        tied.forEach { addNeq(it) }
      }
      flush()
      val status =
        assumption?.let { (solver as AssumingSolver).checkAssuming(it) } ?: solver.check()
      if (status?.isSat != true) return status
    }
    return SolverStatus.SAT
  }

  override fun getHappensBefore(): GlobalRelation {
    val model = solver.model.toMap()
    val rels = GlobalRelation(Event.clkSize) { null }
    events.forEach { e1 ->
      events.forEach { e2 ->
        if (e1.clkId != e2.clkId) {
          if (isSc) {
            val clk1 = model[e1.clkId.clkGlobalVar] as IntLitExpr
            val clk2 = model[e2.clkId.clkGlobalVar] as IntLitExpr
            if (clk1.value < clk2.value) {
              rels[e1.clkId, e2.clkId] = UndetailedReason
            } else {
              check(clk1.value > clk2.value)
              check(rels[e1.clkId, e2.clkId] == null)
            }
          } else {
            val hb = model[hbVars[e1.clkId][e2.clkId]] as BoolLitExpr
            if (hb.value) {
              rels[e1.clkId, e2.clkId] = UndetailedReason
            } else {
              check(rels[e1.clkId, e2.clkId] == null)
            }
          }
        }
      }
    }
    return rels
  }

  override fun getPropagatedClauses(): List<Reason> = emptyList()
}
