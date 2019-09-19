/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.dsl;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslBaseVisitor;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.AssignStmtContext;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.AssumeStmtContext;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.HavocStmtContext;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.StmtContext;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.Stmts.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

final class XcfaStatement {

	private Stmt stmt = null;

	private final Scope scope;
	private final StmtContext context;

	XcfaStatement(final Scope scope, final StmtContext context) {
		this.scope = checkNotNull(scope);
		this.context = checkNotNull(context);
	}

	Stmt instantiate() {
		if(stmt != null) return stmt;
		final StmtCreatorVisitor visitor = new StmtCreatorVisitor(scope, null); //TODO Env
		final Stmt stmt = context.accept(visitor);
		if (stmt == null) {
			throw new AssertionError();
		} else {
			return this.stmt = stmt;
		}
	}

	private static final class StmtCreatorVisitor extends XcfaDslBaseVisitor<Stmt> {

		private final Scope scope;
		private final Env env;

		StmtCreatorVisitor(final Scope scope, final Env env) {
			this.scope = checkNotNull(scope);
			this.env = checkNotNull(env);
		}

		@Override
		public Stmt visitHavocStmt(final HavocStmtContext ctx) {
			final String lhsId = ctx.lhs.getText();
			final Symbol lhsSymbol = scope.resolve(lhsId).get();
			final VarDecl<?> var = (VarDecl<?>) env.eval(lhsSymbol);
			return Havoc(var);
		}

		@Override
		public Stmt visitAssumeStmt(final AssumeStmtContext ctx) {
			final XcfaExpression expression = new XcfaExpression(scope, ctx.cond);
			final Expr<BoolType> expr = TypeUtils.cast(expression.instantiate(env), Bool());
			return Assume(expr);
		}

		@Override
		public Stmt visitAssignStmt(final AssignStmtContext ctx) {
			final String lhsId = ctx.lhs.getText();
			final Symbol lhsSymbol = scope.resolve(lhsId).get();
			final VarDecl<?> var = (VarDecl<?>) env.eval(lhsSymbol);

			final XcfaExpression expression = new XcfaExpression(scope, ctx.value);
			final Expr<?> expr = expression.instantiate(env);

			if (expr.getType().equals(var.getType())) {
				@SuppressWarnings("unchecked")
				final VarDecl<Type> tVar = (VarDecl<Type>) var;
				@SuppressWarnings("unchecked")
				final Expr<Type> tExpr = (Expr<Type>) expr;
				return Assign(tVar, tExpr);
			} else {
				throw new IllegalArgumentException("Type of " + var + " is incompatible with " + expr);
			}
		}

	}

}
