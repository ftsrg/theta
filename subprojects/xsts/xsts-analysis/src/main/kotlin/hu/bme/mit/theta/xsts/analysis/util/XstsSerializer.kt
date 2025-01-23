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
package hu.bme.mit.theta.xsts.analysis.util /*
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

import hu.bme.mit.theta.core.dsl.impl.ExprWriter
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.xsts.XSTS

object XstsSerializer : StmtVisitor<Void?, String> {

  val typeNames =
    mapOf(BoolType.getInstance() to "boolean", IntType.getInstance() to "integer").withDefault {
      it.toString()
    }

  fun serializeXsts(xsts: XSTS): String {
    val builder = StringBuilder()
    for (ctrlVar in xsts.ctrlVars) {
      builder.appendLine("ctrl var ${ctrlVar.name} : integer")
    }
    for (v in xsts.vars - xsts.ctrlVars) {
      builder.appendLine("var ${v.name} : ${typeNames[v.type]}")
    }
    builder.appendLine()

    builder.appendLine(
      "init {\n assume (${serializeExpr(xsts.initFormula)});\n${xsts.init.accept(this, null)}\n}"
    )
    builder.appendLine("trans {\n${xsts.tran.accept(this, null)}\n}")
    builder.appendLine("env {\n${xsts.env.accept(this, null)}\n}")

    return builder.toString()
  }

  fun serializeExpr(expr: Expr<*>): String {
    return ExprWriter.instance().write(expr)
  }

  override fun visit(stmt: SkipStmt?, param: Void?): String {
    return ""
  }

  override fun visit(stmt: AssumeStmt, param: Void?): String {
    return "assume (${serializeExpr(stmt.cond)});"
  }

  override fun <DeclType : Type?> visit(stmt: AssignStmt<DeclType>, param: Void?): String {
    return "${stmt.varDecl.name} := (${serializeExpr(stmt.expr)});"
  }

  override fun <DeclType : Type?> visit(stmt: HavocStmt<DeclType>, param: Void?): String {
    return "havoc ${stmt.varDecl.name};"
  }

  override fun visit(stmt: SequenceStmt, param: Void?): String {
    return stmt.stmts.joinToString("\n") { "${it.accept(this, null)}" }
  }

  override fun visit(stmt: NonDetStmt, param: Void?): String {
    return "choice ${stmt.stmts.joinToString(" or ") { "{\n${it.accept(this, null)}\n}" }}"
  }

  override fun visit(stmt: OrtStmt?, param: Void?): String {
    TODO("Not yet implemented")
  }

  override fun visit(stmt: LoopStmt, param: Void?): String {
    /*
       for i from 1 to y+1 do {
           x:=x-1;
       }
    */
    return """
            for ${stmt.loopVariable.name} from (${serializeExpr(stmt.from)}) to (${serializeExpr(stmt.to)}) do {
                ${stmt.stmt.accept(this, null)}
            }"""
      .trimIndent()
  }

  override fun visit(stmt: IfStmt, param: Void?): String {
    return """
            if (${serializeExpr(stmt.cond)}) {
                ${stmt.then.accept(this, null)}
            } else {
                ${stmt.elze.accept(this, null)}
            }
        """
      .trimIndent()
  }

  override fun <PtrType : Type?, OffsetType : Type?, DeclType : Type?> visit(
    stmt: MemoryAssignStmt<PtrType, OffsetType, DeclType>?,
    param: Void?,
  ): String {
    TODO("Not yet implemented")
  }
}
