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
package hu.bme.mit.theta.xsts.analysis.passes

import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.xsts.XSTS

object XstsGammaTranTransformer {

  fun transform(xsts: XSTS): XSTS {

//    return xsts

    /*
    Transforms XSTS of the form

    tran {
        . . .
        choice {
          a
        } or {
          b
        }
        . . .
    }

    tran {
        . . .
        a
        . . .
    } or {
        . . .
        b
        . . .
    }

    */

    if (xsts.tran.stmts.size != 1) return xsts

    val stmts = (xsts.tran.stmts[0] as SequenceStmt).stmts
    val before = mutableListOf<Stmt>()
    val after = mutableListOf<Stmt>()

    var choice: NonDetStmt? = null
    var found = false
    for (stmt in stmts) {
      if (stmt is NonDetStmt) {
        if (found) return xsts // Two choices found, not handled for now
        found = true
        choice = stmt
      } else {
        if (found) after += stmt else before += stmt
      }
    }

    val newTran = NonDetStmt.of(choice!!.stmts.map { SequenceStmt.of(before + it + after) })

    return XSTS(
      xsts.stateVars,
      xsts.localVars,
      xsts.ctrlVars,
      xsts.init,
      newTran,
      xsts.env,
      xsts.initFormula,
      xsts.prop,
    )
  }
}
