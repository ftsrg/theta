/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.common.cfa.buchi.hoa

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.ltl.dsl.gen.LTLGrammarBaseVisitor
import hu.bme.mit.theta.ltl.dsl.gen.LTLGrammarParser.*

class ToStringVisitor(private val apGeneratorVisitor: APGeneratorVisitor) :
  LTLGrammarBaseVisitor<String?>() {

  var aps: HashMap<String, Expr<BoolType>> = HashMap()
  private var counter = 0

  override fun visitModel(ctx: ModelContext): String {
    return visitImplyExpression(ctx.implyExpression)
  }

  override fun visitImplyExpression(ctx: ImplyExpressionContext): String {
    if (!LTLExprVisitor.visitImplyExpression(ctx)) {
      val name = generateApName()
      val expr = apGeneratorVisitor.visitImplyExpression(ctx)
      aps[name] = expr as Expr<BoolType>
      return name
    }
    return if (ctx.ops.size > 1) {
      visitOrExpr(ctx.ops[0]) + " -> " + visitOrExpr(ctx.ops[1])
    } else {
      visitOrExpr(ctx.ops[0])
    }
  }

  override fun visitOrExpr(ctx: OrExprContext): String {
    if (!LTLExprVisitor.visitOrExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitOrExpr(ctx) as Expr<BoolType>
      return name
    }
    val builder = StringBuilder()
    builder.append(visitAndExpr(ctx.ops[0]))
    for (i in 1 until ctx.ops.size) {
      builder.append(" | ")
      builder.append(visitAndExpr(ctx.ops[i]))
    }
    return builder.toString()
  }

  override fun visitAndExpr(ctx: AndExprContext): String {
    if (!LTLExprVisitor.visitAndExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitAndExpr(ctx)
      return name
    }
    val builder = StringBuilder()
    builder.append(visitNotExpr(ctx.ops[0]))
    for (i in 1 until ctx.ops.size) {
      builder.append(" & ")
      builder.append(visitNotExpr(ctx.ops[i]))
    }
    return builder.toString()
  }

  override fun visitNotExpr(ctx: NotExprContext): String {
    if (!LTLExprVisitor.visitNotExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitNotExpr(ctx)
      return name
    }
    return if (ctx.ops.isNotEmpty()) {
      "! " + visitNotExpr(ctx.ops[0])
    } else {
      visitBinaryLtlExpr(ctx.binaryLtlExpr())
    }
  }

  override fun visitBinaryLtlExpr(ctx: BinaryLtlExprContext): String {
    if (!LTLExprVisitor.visitBinaryLtlExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitBinaryLtlExpr(ctx) as Expr<BoolType>
      return name
    }
    return if (ctx.type != null) {
      (visitBinaryLtlExpr(ctx.ops[0]) +
        " " +
        visitBinaryLtlOp(ctx.type) +
        " " +
        visitBinaryLtlExpr(ctx.ops[1]))
    } else {
      visitLtlExpr(ctx.ltlExpr())
    }
  }

  override fun visitBinaryLtlOp(ctx: BinaryLtlOpContext): String {
    return if (ctx.U_OP() != null) {
      "U"
    } else if (ctx.M_OP() != null) {
      "M"
    } else if (ctx.W_OP() != null) {
      "W"
    } else {
      "R"
    }
  }

  override fun visitLtlExpr(ctx: LtlExprContext): String {
    if (!LTLExprVisitor.visitLtlExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitLtlExpr(ctx) as Expr<BoolType>
      return name
    }
    return if (ctx.ops.size > 0) {
      visitLtlOp(ctx.type) + " " + visitLtlExpr(ctx.ops[0])
    } else {
      visitEqExpr(ctx.eqExpr())
    }
  }

  override fun visitLtlOp(ctx: LtlOpContext): String {
    return if (ctx.F_OP() != null) {
      "F"
    } else if (ctx.G_OP() != null) {
      "G"
    } else {
      "X"
    }
  }

  override fun visitEqExpr(ctx: EqExprContext): String {
    if (!LTLExprVisitor.visitEqExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitEqExpr(ctx) as Expr<BoolType>
      return name
    }
    val builder = StringBuilder()
    builder.append(visitRelationExpr(ctx.ops[0]))
    for (i in 1 until ctx.ops.size) {
      builder.append(visitEqOperator(ctx.oper))
      builder.append(visitRelationExpr(ctx.ops[i]))
    }
    return builder.toString()
  }

  override fun visitEqOperator(ctx: EqOperatorContext): String {
    return if (ctx.EQ() != null) {
      "="
    } else {
      "/="
    }
  }

  override fun visitRelationExpr(ctx: RelationExprContext): String {
    if (!LTLExprVisitor.visitRelationExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitRelationExpr(ctx) as Expr<BoolType>
      return name
    }
    val builder = StringBuilder()
    builder.append(visitAdditiveExpr(ctx.ops[0]))
    for (i in 1 until ctx.ops.size) {
      builder.append(visitRelationOperator(ctx.oper))
      builder.append(visitAdditiveExpr(ctx.ops[i]))
    }
    return builder.toString()
  }

  override fun visitRelationOperator(ctx: RelationOperatorContext): String {
    return if (ctx.LT() != null) {
      "<"
    } else if (ctx.GT() != null) {
      ">"
    } else if (ctx.LEQ() != null) {
      "<="
    } else ">="
  }

  override fun visitAdditiveExpr(ctx: AdditiveExprContext): String {
    if (!LTLExprVisitor.visitAdditiveExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitAdditiveExpr(ctx) as Expr<BoolType>
      return name
    }
    val builder = StringBuilder()
    builder.append(visitMultiplicativeExpr(ctx.ops[0]))
    for (i in 1 until ctx.ops.size) {
      builder.append(visitAdditiveOperator(ctx.opers[i - 1]))
      builder.append(visitMultiplicativeExpr(ctx.ops[i]))
    }
    return builder.toString()
  }

  override fun visitAdditiveOperator(ctx: AdditiveOperatorContext): String {
    return if (ctx.PLUS() != null) {
      "+"
    } else "-"
  }

  override fun visitMultiplicativeExpr(ctx: MultiplicativeExprContext): String {
    if (!LTLExprVisitor.visitMultiplicativeExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitMultiplicativeExpr(ctx) as Expr<BoolType>
      return name
    }
    val builder = StringBuilder()
    builder.append(visitNegExpr(ctx.ops[0]))
    for (i in 1 until ctx.ops.size) {
      builder.append(visitMultiplicativeOperator(ctx.opers[i - 1]))
      builder.append(visitNegExpr(ctx.ops[i]))
    }
    return builder.toString()
  }

  override fun visitMultiplicativeOperator(ctx: MultiplicativeOperatorContext): String {
    return if (ctx.MUL() != null) {
      "*"
    } else if (ctx.MOD() != null) {
      "%"
    } else "/"
  }

  override fun visitNegExpr(ctx: NegExprContext): String {
    if (!LTLExprVisitor.visitNegExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitNegExpr(ctx) as Expr<BoolType>
      return name
    }
    return if (ctx.ops.size > 0) {
      "- " + visitNegExpr(ctx.ops[0])
    } else {
      visitPrimaryExpr(ctx.primaryExpr())
    }
  }

  override fun visitPrimaryExpr(ctx: PrimaryExprContext): String {
    if (!LTLExprVisitor.visitPrimaryExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitPrimaryExpr(ctx) as Expr<BoolType>
      return name
    }
    return if (ctx.parenExpr() != null) {
      visitParenExpr(ctx.parenExpr())
    } else if (ctx.intLitExpr() != null) {
      visitIntLitExpr(ctx.intLitExpr())
    } else visitBoolLitExpr(ctx.boolLitExpr())
  }

  override fun visitBoolLitExpr(ctx: BoolLitExprContext): String {
    return ctx.value.text
  }

  override fun visitParenExpr(ctx: ParenExprContext): String {
    if (!LTLExprVisitor.visitParenExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitParenExpr(ctx) as Expr<BoolType>
      return name
    }
    return if (ctx.variable() != null) {
      visitVariable(ctx.variable())
    } else {
      "(" + visitImplyExpression(ctx.ops[0]) + ")"
    }
  }

  override fun visitIntLitExpr(ctx: IntLitExprContext): String {
    if (!LTLExprVisitor.visitIntLitExpr(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitIntLitExpr(ctx) as Expr<BoolType>
      return name
    }
    return ctx.value.text
  }

  override fun visitVariable(ctx: VariableContext): String {
    if (!LTLExprVisitor.visitVariable(ctx)) {
      val name = generateApName()
      aps[name] = apGeneratorVisitor.visitVariable(ctx) as Expr<BoolType>
      return name
    }
    return ctx.name.text
  }

  private fun generateApName(): String {
    return "ap" + (counter++)
  }
}
