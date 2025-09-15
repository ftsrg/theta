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
package hu.bme.mit.theta.xsts.passes

import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.xsts.XSTS

object XstsNormalizerPass : XstsPass {

  override fun transform(input: XSTS): XSTS {
    val normalizedInit = normalize(input.init)
    val normalizedTran = normalize(input.tran)
    val normalizedEnv = normalize(input.env)

    return XSTS(
      input.ctrlVars,
      normalizedInit,
      normalizedTran,
      normalizedEnv,
      input.initFormula,
      input.prop,
    )
  }

  private fun normalize(stmt: Stmt): NonDetStmt {
    val collector = mutableListOf<MutableList<Stmt>>()
    collector.add(mutableListOf())
    normalize(stmt, collector)
    return NonDetStmt.of(collector.map { SequenceStmt.of(it) }.toList())
  }

  private fun normalize(stmt: Stmt, collector: MutableList<MutableList<Stmt>>) {
    when (stmt) {
      is SequenceStmt -> stmt.stmts.forEach { normalize(it, collector) }
      is NonDetStmt -> {
        val newCollector = mutableListOf<MutableList<Stmt>>()
        stmt.stmts.forEach { nondetBranch ->
          val copy = collector.copy()
          normalize(nondetBranch, copy)
          newCollector.addAll(copy)
        }
        collector.clear()
        collector.addAll(newCollector)
      }

      is SkipStmt -> {}
      else -> collector.forEach { it.add(stmt) }
    }
  }
}

private fun MutableList<MutableList<Stmt>>.copy() = map { it.toMutableList() }.toMutableList()
