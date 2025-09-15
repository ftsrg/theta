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
package hu.bme.mit.theta.xsts.utils

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.dsl.XstsDslManager
import java.io.FileInputStream
import org.junit.jupiter.api.Test

class XSTSVarChangerUnitTest {

  @Test
  fun `xsts variable changing`() {
    var origXsts: XSTS
    FileInputStream("src/test/resources/incrementors.xsts").use { inputStream ->
      origXsts = XstsDslManager.createXsts(inputStream)
    }
    val newX = Decls.Var("x", IntType.getInstance())
    val newY = Decls.Var("y", IntType.getInstance())
    val newXsts = origXsts.copyWithReplacingVars(listOf(newX, newY).associateBy { it.name })

    val origVars =
      setOf(
        StmtUtils.getVars(origXsts.init),
        StmtUtils.getVars(origXsts.tran),
        StmtUtils.getVars(origXsts.env),
      )
    val newVars =
      setOf(
        StmtUtils.getVars(newXsts.init),
        StmtUtils.getVars(newXsts.tran),
        StmtUtils.getVars(newXsts.env),
      )

    assert(!newVars.any { origVars.contains(it) })
  }
}
