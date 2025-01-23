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
package hu.bme.mit.theta.cfa.analysis

import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec
import org.junit.jupiter.api.Test

class CfaCombineExtractUtilsUnitTest {

  val dataState = PredState.of()
  val loc = CFA.builder().createLoc()
  val controlState = CfaState.of<UnitState>(loc, UnitState.getInstance())
  val cfaState = CfaState.of<PredState>(loc, dataState)

  @Test
  fun `Utils work as expected`() {
    assert(cfaState == cfaCombineStates(controlState, dataState))
    assert(cfaExtractControlState(cfaState) == controlState)
    assert(cfaExtractDataState(cfaState) == dataState)
    assert(
      cfaExtractControlPrec(GlobalCfaPrec.create(UnitPrec.getInstance())) ==
        GlobalCfaPrec.create(UnitPrec.getInstance())
    )
  }
}
