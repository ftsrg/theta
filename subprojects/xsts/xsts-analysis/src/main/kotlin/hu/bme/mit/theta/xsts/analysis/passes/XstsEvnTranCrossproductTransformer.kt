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
import java.util.List

object XstsEvnTranCrossproductTransformer {

  fun transform(xsts: XSTS): XSTS {

    /*
    Transforms XSTS of the form

    env {
        a
    } or {
        b
    }

    tran {
        c
    } or {
        d
    }

    to

    env {}

    tran {
        ac
    } or {
        ad
    } or {
        bc
    } or {
        bd
    }

    */

    val envOrig =
      if (xsts.env.stmts.size == 1 && xsts.env.stmts.get(0) is NonDetStmt)
        xsts.env.stmts[0] as NonDetStmt
      else xsts.env
    val tranOrig =
      if (xsts.tran.stmts.size == 1 && xsts.tran.stmts.get(0) is NonDetStmt)
        xsts.tran.stmts[0] as NonDetStmt
      else xsts.tran

    val newTran =
      NonDetStmt.of(
        envOrig.stmts
          .stream()
          .flatMap { e: Stmt ->
            tranOrig.stmts.stream().map { t: Stmt -> SequenceStmt.of(List.of(e, t)) as Stmt }
          }
          .toList()
      )
    val newEnv = NonDetStmt.of(listOf())
    return XSTS(
      xsts.stateVars,
      xsts.localVars,
      xsts.ctrlVars,
      xsts.init,
      newTran,
      newEnv,
      xsts.initFormula,
      xsts.prop,
    )
  }
}
