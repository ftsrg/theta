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
package hu.bme.mit.theta.common.cfa.buchi.hoa

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr
import hu.bme.mit.theta.core.type.enumtype.EnumType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.ltl.dsl.gen.LTLGrammarBaseVisitor
import hu.bme.mit.theta.ltl.dsl.gen.LTLGrammarParser
import hu.bme.mit.theta.ltl.dsl.gen.LTLGrammarParser.*

class APGeneratorVisitor(
  private val vars: Map<String, VarDecl<*>>,
  private val enumTypes: Map<String, EnumType>,
) : LTLGrammarBaseVisitor<Expr<*>?>() {

  override fun visitModel(ctx: ModelContext): Expr<*> {
    return super.visitModel(ctx)!!
  }

  override fun visitImplyExpression(ctx: ImplyExpressionContext): Expr<*> {
    return if (ctx.ops.size > 1) {
      BoolExprs.Imply(
        visitOrExpr(ctx.ops[0]) as Expr<BoolType>,
        visitOrExpr(ctx.ops[1]) as Expr<BoolType>,
      )
    } else visitOrExpr(ctx.ops[0])
  }

  override fun visitOrExpr(ctx: LTLGrammarParser.OrExprContext): Expr<*> {
    if (ctx.ops.size == 1) return visitAndExpr(ctx.ops[0])
    val ops: MutableList<Expr<BoolType>> = ArrayList()
    for (child in ctx.ops) {
      ops.add(visitAndExpr(child))
    }
    return BoolExprs.Or(ops)
  }

  override fun visitAndExpr(ctx: LTLGrammarParser.AndExprContext): Expr<BoolType> {
    if (ctx.ops.size == 1) return visitNotExpr(ctx.ops[0])
    val ops: MutableList<Expr<BoolType>> = ArrayList()
    for (child in ctx.ops) {
      ops.add(visitNotExpr(child))
    }
    return BoolExprs.And(ops)
  }

  override fun visitNotExpr(ctx: LTLGrammarParser.NotExprContext): Expr<BoolType> {
    return if (ctx.ops.size > 0) BoolExprs.Not(visitNotExpr(ctx.ops[0]))
    else visitBinaryLtlExpr(ctx.binaryLtlExpr()) as Expr<BoolType>
  }

  override fun visitBinaryLtlExpr(ctx: BinaryLtlExprContext): Expr<*> {
    return visitLtlExpr(ctx.ltlExpr())
  }

  override fun visitBinaryLtlOp(ctx: BinaryLtlOpContext): Expr<*> {
    return super.visitBinaryLtlOp(ctx)!!
  }

  override fun visitLtlExpr(ctx: LtlExprContext): Expr<*> {
    return visitEqExpr(ctx.eqExpr())
  }

  override fun visitLtlOp(ctx: LtlOpContext): Expr<*> {
    return super.visitLtlOp(ctx)!!
  }

  override fun visitEqExpr(ctx: EqExprContext): Expr<*> {
    return if (ctx.ops.size > 1) {
      if (ctx.oper.EQ() != null)
        AbstractExprs.Eq(visitRelationExpr(ctx.ops[0]), visitRelationExpr(ctx.ops[1]))
      else AbstractExprs.Neq(visitRelationExpr(ctx.ops[0]), visitRelationExpr(ctx.ops[1]))
    } else visitRelationExpr(ctx.ops[0])
  }

  override fun visitEqOperator(ctx: EqOperatorContext): Expr<*> {
    return super.visitEqOperator(ctx)!!
  }

  override fun visitRelationExpr(ctx: LTLGrammarParser.RelationExprContext): Expr<*> {
    return if (ctx.ops.size > 1) {
      if (ctx.oper.LEQ() != null) {
        AbstractExprs.Leq(visitAdditiveExpr(ctx.ops[0]), visitAdditiveExpr(ctx.ops[1]))
      } else if (ctx.oper.GEQ() != null) {
        AbstractExprs.Geq(visitAdditiveExpr(ctx.ops[0]), visitAdditiveExpr(ctx.ops[1]))
      } else if (ctx.oper.LT() != null) {
        AbstractExprs.Lt(visitAdditiveExpr(ctx.ops[0]), visitAdditiveExpr(ctx.ops[1]))
      } else AbstractExprs.Gt(visitAdditiveExpr(ctx.ops[0]), visitAdditiveExpr(ctx.ops[1]))
    } else visitAdditiveExpr(ctx.ops[0])
  }

  override fun visitRelationOperator(ctx: RelationOperatorContext): Expr<*> {
    return super.visitRelationOperator(ctx)!!
  }

  override fun visitAdditiveExpr(ctx: LTLGrammarParser.AdditiveExprContext): Expr<*> {
    var res = visitMultiplicativeExpr(ctx.ops[0])
    for (i in 1 until ctx.ops.size) {
      res =
        if (ctx.opers[i - 1].PLUS() != null) {
          AbstractExprs.Add(res, visitMultiplicativeExpr(ctx.ops[i]))
        } else {
          AbstractExprs.Sub(res, visitMultiplicativeExpr(ctx.ops[i]))
        }
    }
    return res
  }

  override fun visitAdditiveOperator(ctx: AdditiveOperatorContext): Expr<*> {
    return super.visitAdditiveOperator(ctx)!!
  }

  override fun visitMultiplicativeExpr(ctx: LTLGrammarParser.MultiplicativeExprContext): Expr<*> {
    var res = visitNegExpr(ctx.ops[0])
    for (i in 1 until ctx.ops.size) {
      res =
        if (ctx.opers[i - 1].DIV() != null) {
          AbstractExprs.Div(res, visitNegExpr(ctx.ops[i]))
        } else if (ctx.opers[i - 1].MOD() != null) {
          IntExprs.Mod(res as Expr<IntType>, visitNegExpr(ctx.ops[i]) as Expr<IntType>)
        } else {
          AbstractExprs.Mul(res, visitNegExpr(ctx.ops[i]))
        }
    }
    return res
  }

  override fun visitMultiplicativeOperator(ctx: MultiplicativeOperatorContext): Expr<*> {
    return super.visitMultiplicativeOperator(ctx)!!
  }

  override fun visitNegExpr(ctx: LTLGrammarParser.NegExprContext): Expr<*> {
    return if (ctx.ops.size > 0) {
      AbstractExprs.Neg(visitNegExpr(ctx.ops[0]))
    } else visitPrimaryExpr(ctx.primaryExpr())
  }

  override fun visitPrimaryExpr(ctx: LTLGrammarParser.PrimaryExprContext): Expr<*> {
    return if (ctx.boolLitExpr() != null) {
      visitBoolLitExpr(ctx.boolLitExpr())
    } else if (ctx.intLitExpr() != null) {
      visitIntLitExpr(ctx.intLitExpr())
    } else if (ctx.enumLitExpr() != null) {
      visitEnumLitExpr(ctx.enumLitExpr())
    } else visitParenExpr(ctx.parenExpr())
  }

  override fun visitBoolLitExpr(ctx: BoolLitExprContext): Expr<*> {
    return if (ctx.value.text == "true") BoolExprs.True() else BoolExprs.False()
  }

  override fun visitParenExpr(ctx: LTLGrammarParser.ParenExprContext): Expr<*> {
    return if (ctx.variable() != null) visitVariable(ctx.variable())
    else visitImplyExpression(ctx.ops[0])
  }

  override fun visitIntLitExpr(ctx: LTLGrammarParser.IntLitExprContext): Expr<*> {
    return IntExprs.Int(ctx.value.text.toInt())
  }

  override fun visitEnumLitExpr(ctx: EnumLitExprContext): Expr<*> {
    return EnumLitExpr.of(enumTypes[ctx.type.text], ctx.lit.text)
  }

  override fun visitVariable(ctx: LTLGrammarParser.VariableContext): Expr<*> {
    val decl = vars[ctx.name.text]
    if (decl == null) println("Variable [" + ctx.name.text + "] not found")
    return decl!!.ref
  }
}
