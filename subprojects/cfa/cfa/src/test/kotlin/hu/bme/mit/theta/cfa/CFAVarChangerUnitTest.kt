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
package hu.bme.mit.theta.cfa

import hu.bme.mit.theta.cfa.dsl.CfaDslManager
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.inttype.IntType
import java.io.FileInputStream
import org.junit.jupiter.api.Test

class CFAVarChangerUnitTest {

  @Test
  fun `single variable changing`() {
    var origCfa: CFA
    FileInputStream("src/test/resources/counter5_true.cfa").use { inputStream ->
      origCfa = CfaDslManager.createCfa(inputStream)
    }
    val newVar = Decls.Var("x", IntType.getInstance())
    val newCfa = origCfa.copyWithReplacingVars(listOf(newVar).associateBy { it.name })

    assert(!newCfa.vars.any { new -> origCfa.vars.any { old -> new === old } })
    assert(origCfa.vars.first() !== newCfa.vars.first())
  }
}
