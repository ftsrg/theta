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

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Geq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Leq
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.z3.Z3SolverManager
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

class BasicOcCheckerTest {

  companion object {

    @BeforeAll
    @JvmStatic
    fun registerSolver() {
      SolverManager.registerSolverManager(Z3SolverManager.create())
    }
  }

  /** An event of a single memory partition; a null address stands for every address. */
  private class AddressedEvent(
    const: IndexedConstDecl<*>,
    type: EventType,
    pid: Int,
    clkId: Int,
    private val address: Expr<IntType>?,
  ) : Event(const, type, setOf(), pid, clkId) {

    private var addressValue: LitExpr<*>? = null

    override fun enabled(valuation: Valuation): Boolean? =
      super.enabled(valuation).also {
        if (it == true && address != null) addressValue = address.eval(valuation)
      }

    override fun sameMemory(other: Event): Boolean {
      other as AddressedEvent
      if (!super.sameMemory(other)) return false
      return address == null || other.address == null || addressValue == other.addressValue
    }

    override fun interferenceCond(other: Event): Expr<BoolType>? {
      other as AddressedEvent
      if (address == null || other.address == null) return null
      return Eq(address, other.address)
    }
  }

  /**
   * The read can only take the initial value, which is consistent only at the address x = 3 that no
   * write targets. Edges derived for earlier values of x must not survive into the final model.
   */
  @Test
  fun testInitialValueReadAtUnwrittenAddress() {
    val mem = Decls.Var("mem", Int())
    val x = Decls.Const("x", Int())
    val initial = AddressedEvent(mem.getConstDecl(0), EventType.WRITE, 0, 0, null)
    val w1 = AddressedEvent(mem.getConstDecl(1), EventType.WRITE, 0, 1, Int(1))
    val w2 = AddressedEvent(mem.getConstDecl(2), EventType.WRITE, 0, 2, Int(2))
    val r = AddressedEvent(mem.getConstDecl(3), EventType.READ, 1, 3, x.ref)
    val rf = Relation(RelationType.RF, initial, r)

    val checker = BasicOcChecker<AddressedEvent>("Z3:new")
    checker.solver.add(rf.declRef)
    checker.solver.add(And(Geq(x.ref, Int(1)), Leq(x.ref, Int(3))))
    val status =
      checker.check(
        mapOf(mem to mapOf(0 to listOf(initial, w1, w2), 1 to listOf(r))),
        listOf(),
        BooleanGlobalRelation(4) { (i, j) -> i < j },
        mapOf(mem to setOf(rf)),
        mapOf(),
      )

    assertTrue(status?.isSat == true)
    val hb = checker.getHappensBefore()!!
    for (i in 0 until hb.size) {
      for (j in 0 until hb.size) {
        assertFalse(hb[i, j] != null && hb[j, i] != null, "cycle between $i and $j")
      }
    }
  }
}
