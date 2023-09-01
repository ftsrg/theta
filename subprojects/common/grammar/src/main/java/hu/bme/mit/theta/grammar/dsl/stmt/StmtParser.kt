/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.grammar.dsl.stmt

import com.google.common.base.Preconditions
import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Scope
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils
import hu.bme.mit.theta.grammar.ThrowingErrorListener
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper
import hu.bme.mit.theta.grammar.dsl.gen.StmtBaseVisitor
import hu.bme.mit.theta.grammar.dsl.gen.StmtLexer
import hu.bme.mit.theta.grammar.dsl.gen.StmtParser
import hu.bme.mit.theta.grammar.dsl.gen.StmtParser.*
import hu.bme.mit.theta.grammar.textWithWS
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

class StatementWrapper(val content: String, scope: Scope) {

    private val scope: Scope
    private val context: StmtContext

    init {
        this.scope = Preconditions.checkNotNull(scope)
        val lexer = StmtLexer(CharStreams.fromString(content))
        lexer.addErrorListener(ThrowingErrorListener)
        val parser = StmtParser(CommonTokenStream(lexer))
        parser.errorHandler = BailErrorStrategy()
        this.context = Preconditions.checkNotNull<StmtContext>(parser.stmt())
    }

    fun instantiate(env: Env?): Stmt {
        val visitor = StmtCreatorVisitor(scope, env)
        return try {
            context.accept(visitor)
        } catch (e: Exception) {
            System.err.println("Erroneous input: ${context.textWithWS()}")
            throw e
        }
    }

    private class StmtCreatorVisitor(scope: Scope?, env: Env?) : StmtBaseVisitor<Stmt>() {

        private val scope: Scope
        private val env: Env

        init {
            this.scope = Preconditions.checkNotNull(scope)
            this.env = Preconditions.checkNotNull(env)
        }

        override fun visitSkipStmt(ctx: SkipStmtContext): Stmt {
            return SkipStmt.getInstance()
        }

        override fun visitHavocStmt(ctx: HavocStmtContext): Stmt {
            val lhsId: String = ctx.lhs.getText()
            val lhsSymbol = scope.resolve(lhsId).get()
            val `var` = env.eval(lhsSymbol) as VarDecl<*>
            return Stmts.Havoc(`var`)
        }

        override fun visitAssumeStmt(ctx: AssumeStmtContext): Stmt {
            val expression = ExpressionWrapper(scope, ctx.cond.textWithWS())
            val expr: Expr<BoolType> = TypeUtils.cast(expression.instantiate(env), BoolExprs.Bool())
            return Stmts.Assume(expr)
        }

        override fun visitAssignStmt(ctx: AssignStmtContext): Stmt {
            val lhsId: String = ctx.lhs.getText()
            val lhsSymbol = scope.resolve(lhsId).get()
            val `var` = env.eval(lhsSymbol) as VarDecl<*>
            val expression = ExpressionWrapper(scope, ctx.value.textWithWS())
            val expr: Expr<*> = expression.instantiate(env)
            return if (expr.type == `var`.type) {
                val tVar = `var` as VarDecl<Type>
                val tExpr = expr as Expr<Type>
                Stmts.Assign(tVar, tExpr)
            } else {
                throw IllegalArgumentException("Type of $`var` is incompatible with $expr")
            }
        }
    }
}