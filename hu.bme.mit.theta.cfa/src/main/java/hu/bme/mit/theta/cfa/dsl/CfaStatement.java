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
package hu.bme.mit.theta.cfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import hu.bme.mit.theta.cfa.dsl.gen.CfaDslBaseVisitor;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.AssignStmtContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.AssumeStmtContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.HavocStmtContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.StmtContext;
import hu.bme.mit.theta.common.dsl.Environment;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.TypeUtils;

final class CfaStatement {

	private final Scope scope;
	private final StmtContext context;

	public CfaStatement(final Scope scope, final StmtContext context) {
		this.scope = checkNotNull(scope);
		this.context = checkNotNull(context);
	}

	public Stmt instantiate(final Environment env) {
		final StmtCreatorVisitor visitor = new StmtCreatorVisitor(scope, env);
		final Stmt stmt = context.accept(visitor);
		if (stmt == null) {
			throw new AssertionError();
		} else {
			return stmt;
		}
	}

	private static final class StmtCreatorVisitor extends CfaDslBaseVisitor<Stmt> {

		private final Scope scope;
		private final Environment env;

		public StmtCreatorVisitor(final Scope scope, final Environment env) {
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
			final CfaExpression expression = new CfaExpression(scope, ctx.cond);
			final Expr<BoolType> expr = TypeUtils.cast(expression.instantiate(env), Bool());
			return Assume(expr);
		}

		@Override
		public Stmt visitAssignStmt(final AssignStmtContext ctx) {
			final String lhsId = ctx.lhs.getText();
			final Symbol lhsSymbol = scope.resolve(lhsId).get();
			final VarDecl<?> var = (VarDecl<?>) env.eval(lhsSymbol);

			final CfaExpression expression = new CfaExpression(scope, ctx.value);
			final Expr<?> expr = expression.instantiate(env);

			if (expr.getType().equals(var.getType())) {
				@SuppressWarnings("unchecked")
				final VarDecl<Type> tVar = (VarDecl<Type>) var;
				@SuppressWarnings("unchecked")
				final Expr<Type> tExpr = (Expr<Type>) expr;
				return Assign(tVar, tExpr);
			} else {
				throw new IllegalArgumentException("Type of " + var + " is incompatilbe with " + expr);
			}
		}

	}

}
