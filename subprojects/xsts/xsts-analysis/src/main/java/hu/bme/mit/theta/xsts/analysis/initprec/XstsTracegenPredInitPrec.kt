/*
 *  Copyright 2024-2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xsts.analysis.initprec

import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.prod2.Prod2Prec
import hu.bme.mit.theta.core.utils.StmtAtomCollector
import hu.bme.mit.theta.xsts.XSTS

class XstsTracegenPredInitPrec : XstsInitPrec {
  override fun createExpl(xsts: XSTS?): ExplPrec {
    throw RuntimeException("Explicit precision is not supported with guard init precision")
  }

  override fun createPred(xsts: XSTS): PredPrec {
    val tran = xsts.tran
    val ctrlVars = xsts.ctrlVars // TODO add to pred

    val assumes = StmtAtomCollector.collectAtoms(tran)
    // val assumes = StmtAssumeCollector.collectAssumes(tran)
    return PredPrec.of(assumes)
  }

  override fun createProd2ExplPred(xsts: XSTS): Prod2Prec<ExplPrec, PredPrec> {
    throw RuntimeException("Prod2ExplPred precision is not supported with variable list precision")
  }
}
