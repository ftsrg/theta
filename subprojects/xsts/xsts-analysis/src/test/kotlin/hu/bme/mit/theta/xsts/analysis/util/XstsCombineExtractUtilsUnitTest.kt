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

import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.xsts.analysis.XstsState
import org.junit.jupiter.api.Test

class XstsCombineExtractUtilsUnitTest {

  val dataState = PredState.of()
  val controlState = XstsState.of(UnitState.getInstance(), true, false)
  val xstsState = XstsState.of(dataState, true, false)

  @Test
  fun `Utils work as expected`() {
    assert(xstsCombineStates(controlState, dataState) == xstsState)
    assert(xstsExtractControlState(xstsState) == controlState)
    assert(xstsExtractDataState(xstsState) == dataState)
    assert(xstsExtractControlPrec(UnitPrec.getInstance()) == UnitPrec.getInstance())
  }
}
