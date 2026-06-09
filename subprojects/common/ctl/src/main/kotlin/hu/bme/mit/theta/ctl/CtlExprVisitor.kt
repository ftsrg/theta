/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.ctl

import hu.bme.mit.theta.analysis.algorithm.mdd.ctl.CtlExpr
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Div
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mod
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neg
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.ctl.dsl.gen.CtlDslBaseVisitor
import hu.bme.mit.theta.ctl.dsl.gen.CtlDslParser.*

/**
 * Folds a `CtlDsl` parse tree into a [CtlExpr]. Atoms are resolved against the [vars] symbol table;
 * `->` and `<->` are desugared into and/or/not.
 */
class CtlExprVisitor(private val vars: Map<String, VarDecl<*>>) : CtlDslBaseVisitor<CtlExpr>() {

  override fun visitModel(ctx: ModelContext): CtlExpr = visit(ctx.iffExpr())

  // a <-> b  ==  (!a | b) & (!b | a)
  override fun visitIffExpr(ctx: IffExprContext): CtlExpr {
    var acc = visit(ctx.ops[0])
    for (i in 1 until ctx.ops.size) {
      val b = visit(ctx.ops[i])
      acc = CtlExpr.And(CtlExpr.Or(CtlExpr.Not(acc), b), CtlExpr.Or(CtlExpr.Not(b), acc))
    }
    return acc
  }

  // a -> b  ==  !a | b, right-associative
  override fun visitImplyExpr(ctx: ImplyExprContext): CtlExpr {
    var acc = visit(ctx.ops.last())
    for (i in ctx.ops.size - 2 downTo 0) {
      acc = CtlExpr.Or(CtlExpr.Not(visit(ctx.ops[i])), acc)
    }
    return acc
  }

  override fun visitOrExpr(ctx: OrExprContext): CtlExpr =
    ctx.ops.map { visit(it) }.reduce { a, b -> CtlExpr.Or(a, b) }

  override fun visitAndExpr(ctx: AndExprContext): CtlExpr =
    ctx.ops.map { visit(it) }.reduce { a, b -> CtlExpr.And(a, b) }

  override fun visitNotExpr(ctx: NotExprContext): CtlExpr = CtlExpr.Not(visit(ctx.op))

  override fun visitExExpr(ctx: ExExprContext): CtlExpr = CtlExpr.EX(visit(ctx.op))

  override fun visitEfExpr(ctx: EfExprContext): CtlExpr = CtlExpr.EF(visit(ctx.op))

  override fun visitEgExpr(ctx: EgExprContext): CtlExpr = CtlExpr.EG(visit(ctx.op))

  override fun visitAxExpr(ctx: AxExprContext): CtlExpr = CtlExpr.AX(visit(ctx.op))

  override fun visitAfExpr(ctx: AfExprContext): CtlExpr = CtlExpr.AF(visit(ctx.op))

  override fun visitAgExpr(ctx: AgExprContext): CtlExpr = CtlExpr.AG(visit(ctx.op))

  override fun visitQuantPassthrough(ctx: QuantPassthroughContext): CtlExpr = visit(ctx.quantExpr())

  override fun visitEuExpr(ctx: EuExprContext): CtlExpr = CtlExpr.EU(visit(ctx.l), visit(ctx.r))

  override fun visitAuExpr(ctx: AuExprContext): CtlExpr = CtlExpr.AU(visit(ctx.l), visit(ctx.r))

  override fun visitParenCtlExpr(ctx: ParenCtlExprContext): CtlExpr = visit(ctx.iffExpr())

  override fun visitAtomExpr(ctx: AtomExprContext): CtlExpr =
    CtlExpr.Atom(buildBool(ctx.atom().relationExpr()))

  private fun buildBool(ctx: RelationExprContext): Expr<BoolType> {
    val left = buildArith(ctx.ops[0])
    if (ctx.oper == null) {
      if (left.type !is BoolType) {
        throw CtlParseException("Atom '${ctx.text}' is not a boolean expression")
      }
      @Suppress("UNCHECKED_CAST") return left as Expr<BoolType>
    }
    val right = buildArith(ctx.ops[1])
    val op = ctx.oper
    val result =
      when {
        op.EQ() != null -> Eq(left, right)
        op.NEQ() != null -> Neq(left, right)
        op.LT() != null -> Lt(left, right)
        op.GT() != null -> Gt(left, right)
        op.LEQ() != null -> Leq(left, right)
        op.GEQ() != null -> Geq(left, right)
        else -> throw CtlParseException("Unknown relational operator '${op.text}'")
      }
    @Suppress("UNCHECKED_CAST") return result as Expr<BoolType>
  }

  private fun buildArith(ctx: AdditiveExprContext): Expr<*> {
    var acc = buildMul(ctx.ops[0])
    for (i in 1 until ctx.ops.size) {
      val rhs = buildMul(ctx.ops[i])
      acc = if (ctx.opers[i - 1].PLUS() != null) Add(acc, rhs) else Sub(acc, rhs)
    }
    return acc
  }

  private fun buildMul(ctx: MultiplicativeExprContext): Expr<*> {
    var acc = buildPrimary(ctx.ops[0])
    for (i in 1 until ctx.ops.size) {
      val rhs = buildPrimary(ctx.ops[i])
      val op = ctx.opers[i - 1]
      acc =
        when {
          op.MUL() != null -> Mul(acc, rhs)
          op.DIV() != null -> Div(acc, rhs)
          else -> Mod(acc, rhs)
        }
    }
    return acc
  }

  private fun buildPrimary(ctx: PrimaryArithContext): Expr<*> =
    when (ctx) {
      is IntLitExprContext -> Int(ctx.value.text)
      is BoolLitExprContext -> if (ctx.value.text == "true") True() else False()
      is VarExprContext -> {
        val name = ctx.name.text
        (vars[name] ?: throw CtlParseException("Unknown variable '$name'")).ref
      }
      is NegArithExprContext -> Neg(buildPrimary(ctx.op))
      is ParenArithExprContext -> buildArith(ctx.additiveExpr())
      else -> throw CtlParseException("Unknown arithmetic expression '${ctx.text}'")
    }
}
