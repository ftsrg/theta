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

import hu.bme.mit.theta.ltl.dsl.gen.LTLGrammarBaseVisitor
import hu.bme.mit.theta.ltl.dsl.gen.LTLGrammarParser
import hu.bme.mit.theta.ltl.dsl.gen.LTLGrammarParser.*
import org.antlr.v4.runtime.ParserRuleContext

/**
 * Returns whether an AST element represents an LTL expression that has no temporal operators. We
 * need to convert all these into atomic propositions that Spot can interpret. So in the AST, the F
 * G(not err), the largest expression (not err) will be converted to atomic proposition ap0. The
 * resulting LTL expression, which now Spot can interpret, is F G ap0. Whether there is an LTL
 * expression, is returned by LTLExprVisitor. The link is stored in APGeneratorVisitor's result.
 */
object LTLExprVisitor : LTLGrammarBaseVisitor<Boolean?>() {

  var ltl: HashMap<ParserRuleContext, Boolean?> = HashMap()

  override fun visitModel(ctx: ModelContext): Boolean {
    return super.visitModel(ctx)!!
  }

  override fun visitImplyExpression(ctx: ImplyExpressionContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    for (op in ctx.ops) {
      if (visitOrExpr(op)) {
        ltl[ctx] = true
        return true
      }
    }
    ltl[ctx] = false
    return false
  }

  override fun visitAndExpr(ctx: LTLGrammarParser.AndExprContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    for (op in ctx.ops) {
      if (visitNotExpr(op)) {
        ltl[ctx] = true
        return true
      }
    }
    ltl[ctx] = false
    return false
  }

  override fun visitNotExpr(ctx: LTLGrammarParser.NotExprContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    for (op in ctx.ops) {
      if (visitNotExpr(op)) {
        ltl[ctx] = true
        return true
      }
    }
    if (ctx.binaryLtlExpr() != null && visitBinaryLtlExpr(ctx.binaryLtlExpr())) {
      ltl[ctx] = true
      return true
    }
    ltl[ctx] = false
    return false
  }

  override fun visitBinaryLtlExpr(ctx: BinaryLtlExprContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    if (ctx.type != null) {
      ltl[ctx] = true
      return true
    }
    val child = visitLtlExpr(ctx.ltlExpr())
    ltl[ctx] = child
    return child
  }

  override fun visitBinaryLtlOp(ctx: BinaryLtlOpContext): Boolean {
    return false
  }

  override fun visitLtlExpr(ctx: LtlExprContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    if (ctx.type != null) {
      ltl[ctx] = true
      return true
    }
    val child = visitEqExpr(ctx.eqExpr())
    ltl[ctx] = child
    return child
  }

  override fun visitLtlOp(ctx: LtlOpContext): Boolean {
    return false
  }

  override fun visitEqExpr(ctx: EqExprContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    for (op in ctx.ops) {
      if (visitRelationExpr(op)) {
        ltl[ctx] = true
        return true
      }
    }
    ltl[ctx] = false
    return false
  }

  override fun visitEqOperator(ctx: EqOperatorContext): Boolean {
    return false
  }

  override fun visitRelationExpr(ctx: LTLGrammarParser.RelationExprContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    for (op in ctx.ops) {
      if (visitAdditiveExpr(op)) {
        ltl[ctx] = true
        return true
      }
    }
    ltl[ctx] = false
    return false
  }

  override fun visitRelationOperator(ctx: RelationOperatorContext): Boolean {
    return false
  }

  override fun visitAdditiveExpr(ctx: LTLGrammarParser.AdditiveExprContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    for (op in ctx.ops) {
      if (visitMultiplicativeExpr(op)) {
        ltl[ctx] = true
        return true
      }
    }
    ltl[ctx] = false
    return false
  }

  override fun visitAdditiveOperator(ctx: AdditiveOperatorContext): Boolean {
    return false
  }

  override fun visitMultiplicativeExpr(ctx: LTLGrammarParser.MultiplicativeExprContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    for (op in ctx.ops) {
      if (visitNegExpr(op)) {
        ltl[ctx] = true
        return true
      }
    }
    ltl[ctx] = false
    return false
  }

  override fun visitMultiplicativeOperator(ctx: MultiplicativeOperatorContext): Boolean {
    return false
  }

  override fun visitNegExpr(ctx: LTLGrammarParser.NegExprContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    for (op in ctx.ops) {
      if (visitNegExpr(op)) {
        ltl[ctx] = true
        return true
      }
    }
    if (ctx.primaryExpr() != null && visitPrimaryExpr(ctx.primaryExpr())) {
      ltl[ctx] = true
      return true
    }
    ltl[ctx] = false
    return false
  }

  override fun visitPrimaryExpr(ctx: LTLGrammarParser.PrimaryExprContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    var child = false
    if (ctx.boolLitExpr() != null) child = visitBoolLitExpr(ctx.boolLitExpr())
    if (ctx.intLitExpr() != null) child = visitIntLitExpr(ctx.intLitExpr())
    if (ctx.parenExpr() != null) child = visitParenExpr(ctx.parenExpr())
    ltl[ctx] = child
    return child
  }

  override fun visitBoolLitExpr(ctx: BoolLitExprContext): Boolean {
    return false
  }

  override fun visitParenExpr(ctx: LTLGrammarParser.ParenExprContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    for (op in ctx.ops) {
      if (visitImplyExpression(op)) {
        ltl[ctx] = true
        return true
      }
    }
    ltl[ctx] = false
    return false
  }

  override fun visitIntLitExpr(ctx: LTLGrammarParser.IntLitExprContext): Boolean {
    return false
  }

  override fun visitVariable(ctx: LTLGrammarParser.VariableContext): Boolean {
    return false
  }

  override fun visitOrExpr(ctx: LTLGrammarParser.OrExprContext): Boolean {
    if (ltl[ctx] != null) return ltl[ctx]!!
    for (op in ctx.ops) {
      if (visitAndExpr(op)) {
        ltl[ctx] = true
        return true
      }
    }
    ltl[ctx] = false
    return false
  }
}
