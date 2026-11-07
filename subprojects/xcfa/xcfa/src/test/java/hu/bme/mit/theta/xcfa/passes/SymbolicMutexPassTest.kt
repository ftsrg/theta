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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.stmt.Stmts.Havoc
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Write
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToNeutralBvLitExpr
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test

class SymbolicMutexPassTest {
  private val h = Var("h", Int())
  private val alias = Var("alias", Int())
  private val ret = Var("ret", Int())
  private val address = Int(10)
  private val attr = Int(20)

  private fun call(name: String, vararg args: Expr<*>) =
    InvokeLabel(name, listOf(ret.ref) + args, EmptyMetaData, isLibraryFunction = true)

  private class Program(operations: List<XcfaLabel>, vars: List<VarDecl<*>>) {
    val model = XcfaBuilder("mutex")
    val main = XcfaProcedureBuilder("main", ProcedurePassManager())
    val targets = operations.indices.map { XcfaLocation("after_$it", metadata = EmptyMetaData) }
    var values = MutableValuation()
    val tid: VarDecl<IntType>

    init {
      main.createInitLoc()
      model.addEntryPoint(main, emptyList())
      vars.forEach { main.addVar(it) }
      operations.forEachIndexed { i, label ->
        main.addEdge(
          XcfaEdge(if (i == 0) main.initLoc else targets[i - 1], targets[i], label, EmptyMetaData)
        )
      }
      SymbolicMutexPass().runChecked(main)
      model.getVars().forEach { values.put(it.wrappedVar, it.initValue!!) }
      @Suppress("UNCHECKED_CAST")
      tid = main.getVars().single { it.name.startsWith("__theta_mutex_tid_") } as VarDecl<IntType>
      values.put(tid, Int(0))
    }

    fun alternatives(operation: Int) = main.getEdges().filter { it.target == targets[operation] }

    fun step(operation: Int, thread: Int = 0): Boolean {
      values.put(tid, Int(thread))
      val successors =
        alternatives(operation).mapNotNull { edge ->
          val result = MutableValuation.copyOf(values)
          for (label in edge.getFlatLabels()) {
            val stmt = (label as StmtLabel).stmt
            when (stmt) {
              is AssumeStmt -> if (stmt.cond.eval(result) != True()) return@mapNotNull null
              is AssignStmt<*> -> result.put(stmt.varDecl, stmt.expr.eval(result))
            }
          }
          result
        }
      assertTrue(successors.size <= 1, "alternatives must be mutually exclusive")
      if (successors.isEmpty()) return false
      values = successors.single()
      return true
    }

    @Suppress("UNCHECKED_CAST")
    fun read(prefix: String, vararg indices: LitExpr<*>): LitExpr<*> {
      var expr: Expr<*> =
        model.getVars().single { it.wrappedVar.name.startsWith(prefix) }.wrappedVar.ref
      indices.forEach { expr = Read(expr as Expr<ArrayType<Type, Type>>, it as Expr<Type>) }
      return expr.eval(values)
    }
  }

  @Test
  fun normalMutexTracksAliasesAndIgnoresForeignUnlocks() {
    val p =
      Program(
        listOf(
          MutexLockLabel(h.ref),
          MutexTryLockLabel(alias.ref, ret),
          MutexUnlockLabel(alias.ref),
          MutexUnlockLabel(address),
        ),
        listOf(h, alias, ret),
      )
    p.values.put(h, address).put(alias, address)
    assertTrue(p.step(0))
    assertFalse(p.step(0))
    assertTrue(p.step(1, 1))
    assertEquals(Int(16), p.values.eval(ret).get())
    assertTrue(p.step(2, 1))
    assertEquals(Int(0), p.read("__theta_simple_mutexes", address))
    assertEquals(2, p.alternatives(2).size)
    assertTrue(p.step(3))
    assertEquals(Int(-1), p.read("__theta_simple_mutexes", address))
    assertTrue(p.step(1, 1))
    assertEquals(Int(0), p.values.eval(ret).get())
    assertEquals(Int(1), p.read("__theta_simple_mutexes", address))
    assertFalse(
      p.model.getVars().any {
        it.wrappedVar.name.startsWith("__theta_recursive") ||
          it.wrappedVar.name.startsWith("__theta_acquisitions")
      }
    )
  }

  @Test
  fun recursiveMutexCopiesAttributesAndReleasesOnlyItsLastAcquisition() {
    val p =
      Program(
        listOf(
          call("pthread_mutexattr_init", attr),
          call("pthread_mutexattr_settype", attr, Int(1)),
          call("pthread_mutex_init", h.ref, attr),
          call("pthread_mutexattr_destroy", attr),
          MutexLockLabel(h.ref),
          MutexUnlockLabel(h.ref),
          MutexTryLockLabel(h.ref, ret),
          call("pthread_mutex_init", h.ref, Int(0)),
        ),
        listOf(h, ret),
      )
    p.values.put(h, address)
    (0..3).forEach { assertTrue(p.step(it)) }
    assertEquals(False(), p.read("__theta_recursive", attr))
    assertEquals(True(), p.read("__theta_recursive", address))
    assertTrue(p.step(4))
    assertTrue(p.step(4))
    assertEquals(Int(2), p.read("__theta_acquisitions", address))
    assertTrue(p.step(5))
    assertEquals(Int(1), p.read("__theta_acquisitions", address))
    assertTrue(p.step(6, 1))
    assertEquals(Int(16), p.values.eval(ret).get())
    assertTrue(p.step(6))
    assertEquals(Int(0), p.values.eval(ret).get())
    assertTrue(p.step(5, 1))
    assertEquals(Int(2), p.read("__theta_acquisitions", address))
    assertTrue(p.step(5))
    assertTrue(p.step(5))
    assertEquals(Int(-1), p.read("__theta_simple_mutexes", address))
    assertEquals(Int(0), p.read("__theta_acquisitions", address))
    assertEquals(3, p.alternatives(5).size)
    assertTrue(p.step(6, 1))
    assertEquals(Int(0), p.values.eval(ret).get())
    assertTrue(p.step(5, 1))
    assertTrue(p.step(7))
    assertEquals(False(), p.read("__theta_recursive", address))
    assertTrue(p.step(4))
    assertFalse(p.step(4))
  }

  @Test
  @Suppress("UNCHECKED_CAST")
  fun rwUnlockDecrementsBothKindsWithoutGoingBelowZero() {
    val p = Program(listOf(RWLockUnlockLabel(h.ref)), listOf(h))
    p.values.put(h, address)
    val locks =
      p.model.getVars().single { it.wrappedVar.name.startsWith("__theta_rw_mutexes") }.wrappedVar
        as VarDecl<ArrayType<IntType, ArrayType<IntType, ArrayType<IntType, IntType>>>>
    fun setCount(mode: Int, count: Int) {
      val update =
        Write(
          locks.ref,
          address,
          Write(
            Read(locks.ref, address),
            Int(mode),
            Write(Read(Read(locks.ref, address), Int(mode)), Int(0), Int(count)),
          ),
        )
      p.values.put(locks, update.eval(p.values))
    }
    setCount(0, 2)
    setCount(1, 1)
    assertTrue(p.step(0))
    assertEquals(Int(1), p.read("__theta_rw_mutexes", address, Int(0), Int(0)))
    assertEquals(Int(0), p.read("__theta_rw_mutexes", address, Int(1), Int(0)))
    assertTrue(p.step(0))
    assertTrue(p.step(0))
    assertEquals(Int(0), p.read("__theta_rw_mutexes", address, Int(0), Int(0)))
    assertEquals(Int(0), p.read("__theta_rw_mutexes", address, Int(1), Int(0)))
  }

  @Test
  fun readWriteLocksRetainOtherReadersAndCountRepeatedReads() {
    val p =
      Program(
        listOf(RWLockReadLockLabel(h.ref), RWLockWriteLockLabel(h.ref), RWLockUnlockLabel(h.ref)),
        listOf(h),
      )
    p.values.put(h, address)
    assertTrue(p.step(0))
    assertTrue(p.step(0))
    assertTrue(p.step(0, 1))
    assertEquals(Int(2), p.read("__theta_rw_mutexes", address, Int(0), Int(0)))
    assertFalse(p.step(1, 2))
    assertTrue(p.step(2))
    assertFalse(p.step(1, 2))
    assertTrue(p.step(2))
    assertTrue(p.step(2))
    assertEquals(Int(0), p.read("__theta_rw_mutexes", address, Int(0), Int(0)))
    assertEquals(Int(1), p.read("__theta_rw_mutexes", address, Int(0), Int(1)))
    assertFalse(p.step(1, 2))
    assertTrue(p.step(2, 1))
    assertTrue(p.step(1, 2))
    assertFalse(p.step(0, 2))
    assertFalse(p.step(1, 2))
    assertTrue(p.step(2, 2))
    assertTrue(p.step(0))
    assertEquals(4, p.alternatives(2).size)
    assertFalse(p.model.getVars().any { it.wrappedVar.name.startsWith("__theta_simple_mutexes") })
  }

  @Test
  fun bitvectorHandlesAndAttributeSettingsAreSupported() {
    val bv = bigIntegerToNeutralBvLitExpr(BigInteger.TEN, 64)
    val pointer = Var("pointer", bv.type)
    val attributes = bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(20), 64)
    val p =
      Program(
        listOf(
          call(
            "pthread_mutexattr_settype",
            attributes,
            bigIntegerToNeutralBvLitExpr(BigInteger.ONE, 32),
          ),
          call("pthread_mutex_init", pointer.ref, attributes),
          MutexLockLabel(pointer.ref),
          MutexUnlockLabel(pointer.ref),
        ),
        listOf(pointer, ret),
      )
    p.values.put(pointer, bv)
    (0..3).forEach { assertTrue(p.step(it)) }
    assertEquals(Int(-1), p.read("__theta_simple_mutexes", bv))
  }

  private fun procedure(
    model: XcfaBuilder,
    name: String,
    manager: ProcedurePassManager = ProcedurePassManager(),
  ): XcfaProcedureBuilder =
    XcfaProcedureBuilder(name, manager).also {
      model.addProcedure(it)
      it.createInitLoc()
      it.createFinalLoc()
    }

  private fun XcfaProcedureBuilder.edge(label: XcfaLabel) =
    addEdge(XcfaEdge(initLoc, finalLoc.get(), SequenceLabel(listOf(label)), EmptyMetaData))

  @Test
  fun fullyResolvableAlternativesKeepTheExistingEncoding() {
    val model = XcfaBuilder("finite")
    val main = procedure(model, "main")
    model.addEntryPoint(main, emptyList())
    main.addVar(h)
    val join = XcfaLocation("join", metadata = EmptyMetaData)
    listOf(10, 20).forEach {
      main.addEdge(XcfaEdge(main.initLoc, join, StmtLabel(Assign(h, Int(it))), EmptyMetaData))
    }
    main.addEdge(XcfaEdge(join, main.finalLoc.get(), MutexLockLabel(h.ref), EmptyMetaData))
    AmbiguousMutexPass().runChecked(main)
    assertTrue(model.getVars().isEmpty())
    assertTrue(main.getParams().isEmpty())
    assertEquals(
      setOf(Int(10), Int(20)),
      main
        .getEdges()
        .flatMap { it.getFlatLabels() }
        .filterIsInstance<MutexLockLabel>()
        .map { it.lock }
        .toSet(),
    )
  }

  @Test
  fun unresolvedHandleInAnotherProcedureConvertsLiteralMutexesToo() {
    val model = XcfaBuilder("fallback")
    val main = procedure(model, "main")
    val worker = procedure(model, "worker")
    model.addEntryPoint(main, emptyList())
    main.edge(MutexLockLabel(address))
    worker.addVar(h)
    worker.edge(SequenceLabel(listOf(StmtLabel(Havoc(h)), MutexLockLabel(h.ref))))
    val pass = AmbiguousMutexPass()
    pass.runChecked(main)
    pass.runChecked(worker)
    assertTrue(model.getVars().any { it.wrappedVar.name.startsWith("__theta_simple_mutexes") })
    assertTrue(
      model
        .getProcedures()
        .flatMap { it.getEdges() }
        .flatMap { it.getFlatLabels() }
        .none { it is FenceLabel }
    )
  }

  @Test
  fun threadStartsAllocateDistinctIdsAndCallsForwardTheirCallerId() {
    val model = XcfaBuilder("threads")
    val main = procedure(model, "main")
    val worker = procedure(model, "worker")
    val helper = procedure(model, "helper")
    model.addEntryPoint(main, emptyList())
    helper.addVar(h)
    helper.edge(MutexLockLabel(h.ref))
    worker.edge(InvokeLabel("helper", emptyList(), EmptyMetaData))
    val first = Var("first", Int())
    val second = Var("second", Int())
    main.addVar(first)
    main.addVar(second)
    main.edge(
      SequenceLabel(
        listOf(
          StartLabel("worker", emptyList(), first, EmptyMetaData),
          StartLabel("worker", emptyList(), second, EmptyMetaData),
        )
      )
    )
    SymbolicMutexPass().runChecked(main)
    assertEquals(ParamDirection.IN, worker.getParams().last().second)
    assertEquals(ParamDirection.IN, helper.getParams().last().second)
    val call =
      worker.getEdges().flatMap { it.getFlatLabels() }.filterIsInstance<InvokeLabel>().single()
    assertEquals(worker.getParams().last().first.ref, call.params.last())
    val values = MutableValuation()
    val ids = mutableListOf<LitExpr<*>>()
    main
      .getEdges()
      .sortedBy { if (it.source == main.initLoc) 0 else 1 }
      .forEach { edge ->
        edge.getFlatLabels().forEach { label ->
          if (label is StmtLabel && label.stmt is AssignStmt<*>) {
            val assign = label.stmt as AssignStmt<*>
            values.put(assign.varDecl, assign.expr.eval(values))
          } else if (label is StartLabel) ids.add(label.params.last().eval(values))
        }
      }
    assertEquals(listOf(Int(1), Int(2)), ids)
  }

  @Test
  fun multipleRootsInitializeMutexStateOnceBeforeStartingTheRoots() {
    val model = XcfaBuilder("roots")
    val first = procedure(model, "first")
    val second = procedure(model, "second")
    model.addEntryPoint(first, emptyList())
    model.addEntryPoint(second, emptyList())
    first.edge(MutexLockLabel(address))
    second.edge(MutexUnlockLabel(address))
    SymbolicMutexPass().runChecked(first)
    val built = model.build()
    val bootstrap = built.initProcedures.single().first
    val starts = bootstrap.edges.flatMap { it.getFlatLabels() }.filterIsInstance<StartLabel>()
    assertEquals(listOf(Int(0), Int(1)), starts.map { it.params.last() })
    assertEquals(
      1,
      bootstrap.edges
        .flatMap { it.getFlatLabels() }
        .filterIsInstance<StmtLabel>()
        .count {
          (it.stmt as? AssignStmt<*>)?.varDecl?.name?.startsWith("__theta_simple_mutexes") == true
        },
    )
  }

  @Test
  fun callableEntryPointHasASeparateRootInitializationCopy() {
    val model = XcfaBuilder("recursive_root")
    val manager = ProcedurePassManager(listOf(AmbiguousMutexPass()), listOf(EmptyEdgeRemovalPass()))
    val main = procedure(model, "main", manager)
    model.addEntryPoint(main, emptyList())
    main.addVar(h)
    main.edge(
      SequenceLabel(listOf(MutexLockLabel(h.ref), InvokeLabel("main", emptyList(), EmptyMetaData)))
    )
    val built = model.build()
    assertNotEquals("main", built.initProcedures.single().first.name)
    assertEquals(1, built.procedures.single { it.name == "main" }.params.size)
    assertTrue(built.initProcedures.single().first.params.isEmpty())
  }

  @Test
  fun solverRejectsAcquisitionThroughAnEqualSymbolicAliasByAnotherThread() {
    val p = Program(listOf(MutexLockLabel(h.ref), MutexLockLabel(alias.ref)), listOf(h, alias))
    val stmts =
      p.model.getVars().map { Assign(it.wrappedVar.typed, it.initValue!!.typed) } +
        listOf(Assign(p.tid, Int(0)), Assume(Eq(h.ref, alias.ref))) +
        p.alternatives(0).single().label.toStmt() +
        Assign(p.tid, Int(1)) +
        p.alternatives(1).single().label.toStmt()
    val unfolded = StmtUtils.toExpr(SequenceStmt.of(stmts), VarIndexingFactory.indexing(0))
    Z3SolverFactory.getInstance().createSolver().use { solver ->
      solver.add(PathUtils.unfold(And(unfolded.exprs), 0))
      assertTrue(solver.check().isUnsat)
    }
  }

  @Suppress("UNCHECKED_CAST")
  private val VarDecl<*>.typed: VarDecl<Type>
    get() = this as VarDecl<Type>

  @Suppress("UNCHECKED_CAST")
  private val Expr<*>.typed: Expr<Type>
    get() = this as Expr<Type>
}
