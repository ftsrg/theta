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
package hu.bme.mit.theta.analysis.algorithm

import hu.bme.mit.theta.analysis.algorithm.chc.HornChecker
import hu.bme.mit.theta.common.OsHelper
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.Relation
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.plus
import hu.bme.mit.theta.core.type.inttype.IntExprs.Add
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.Test

class HornTest {

  @Test
  fun testHornUnsafe() {
    Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX))

    val inv = Relation("inv", Int())
    val p0 = Param("P0", Int())
    val p1 = Param("P1", Int())
    inv(p0.ref) += Eq(p0.ref, Int(0))
    inv(p1.ref) += inv(p0.ref).expr + Eq(p1.ref, Add(p0.ref, Int(1)))
    !(inv(p0.ref) with Eq(p0.ref, Int(5)))

    val checker = HornChecker(listOf(inv), Z3SolverFactory.getInstance(), NullLogger.getInstance())
    Assertions.assertTrue(checker.check().isUnsafe)
  }

  @Test
  fun testHornSafe() {
    Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX))

    val inv = Relation("inv", Int())
    val p0 = Param("P0", Int())
    val p1 = Param("P1", Int())
    inv(p0.ref) += Eq(p0.ref, Int(0))
    inv(p1.ref) += inv(p0.ref).expr + Eq(p1.ref, Add(p0.ref, Int(2)))
    !(inv(p0.ref) with Eq(p0.ref, Int(5)))

    val checker = HornChecker(listOf(inv), Z3SolverFactory.getInstance(), NullLogger.getInstance())
    Assertions.assertTrue(checker.check().isSafe)
  }
}
