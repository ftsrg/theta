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
package hu.bme.mit.theta.cfa.analysis.prec

import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.booltype.BoolType
import org.junit.jupiter.api.Test

class RefutationToGlobalCfaPrecUnitTest {

  val refToPrec = ItpRefToExplPrec()
  val loc = CFA.builder().createLoc()!!
  val refToCfaPrec = RefutationToGlobalCfaPrec(refToPrec, loc)
  val var1 = Decls.Var<BoolType>("b1", BoolType.getInstance())
  val var2 = Decls.Var<BoolType>("b2", BoolType.getInstance())

  @Test
  fun `Result precision simply contains what's in the refutation`() {
    val refutation = ItpRefutation.sequence(listOf(var1.ref))

    val result = refToCfaPrec.toPrec(refutation, 0)

    assert(result.prec.vars.size == 1)
    assert(result.prec.vars.contains(var1))
  }

  @Test
  fun `Join should simply join the two expl precisions`() {
    val prec1 = ExplPrec.of(listOf(var1))
    val prec2 = ExplPrec.of(listOf(var2))
    val cfaPrec1 = GlobalCfaPrec.create(prec1)
    val cfaPrec2 = GlobalCfaPrec.create(prec2)

    val result = refToCfaPrec.join(cfaPrec1, cfaPrec2)

    assert(result.prec.vars.contains(var1) && result.prec.vars.contains(var2))
  }
}
