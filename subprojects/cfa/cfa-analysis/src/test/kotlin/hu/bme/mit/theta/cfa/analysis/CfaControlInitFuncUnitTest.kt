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

import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.cfa.analysis.prec.LocalCfaPrec
import org.junit.jupiter.api.Test

class CfaControlInitFuncUnitTest {

  @Test
  fun `Init func should return 1 element UnitState set`() {
    val cfaLoc = CFA.builder().createLoc()
    val initFunc = cfaControlInitFunc<PredPrec>(cfaLoc)
    val initStates = initFunc.getInitStates(LocalCfaPrec.create<PredPrec>(PredPrec.of()))
    assert(initStates.size == 1)
    assert(initStates.all { it.state == UnitState.getInstance() })
  }
}
