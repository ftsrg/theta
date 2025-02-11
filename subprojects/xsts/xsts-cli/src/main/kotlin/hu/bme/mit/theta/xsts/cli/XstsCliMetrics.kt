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
package hu.bme.mit.theta.xsts.cli

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.groups.provideDelegate
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.StmtCounterVisitor
import hu.bme.mit.theta.xsts.cli.optiongroup.InputOptions

class XstsCliMetrics : CliktCommand(name = "metrics") {

  private val inputOptions by InputOptions()

  override fun run() {
    val logger = ConsoleLogger(Logger.Level.VERBOSE)
    val xsts = inputOptions.loadXsts()
    logger.write(Logger.Level.RESULT, "Vars: %s%n", xsts.vars.size)
    logger.write(
      Logger.Level.RESULT,
      "  Bool vars: %s%n",
      xsts.vars.stream().filter { v: VarDecl<*> -> v.type is BoolType }.count(),
    )
    logger.write(
      Logger.Level.RESULT,
      "  Int vars: %s%n",
      xsts.vars.stream().filter { v: VarDecl<*> -> v.type is IntType }.count(),
    )
    logger.write(
      Logger.Level.RESULT,
      "  Bitvector vars: %s%n",
      xsts.vars.stream().filter { v: VarDecl<*> -> v.type is BvType }.count(),
    )
    logger.write(
      Logger.Level.RESULT,
      "  Array vars: %s%n",
      xsts.vars.stream().filter { v: VarDecl<*> -> v.type is ArrayType<*, *> }.count(),
    )
    logger.write(Logger.Level.RESULT, "  Ctrl vars: %s%n", xsts.ctrlVars.size)
    logger.write(
      Logger.Level.RESULT,
      "Tran statements: %s%n",
      xsts.tran.accept<Void?, Int>(StmtCounterVisitor.getInstance(), null),
    )
    logger.write(
      Logger.Level.RESULT,
      "Env statements: %s%n",
      xsts.env.accept<Void?, Int>(StmtCounterVisitor.getInstance(), null),
    )
    logger.write(
      Logger.Level.RESULT,
      "Init statements: %s%n",
      xsts.init.accept<Void?, Int>(StmtCounterVisitor.getInstance(), null),
    )
  }
}
