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
package hu.bme.mit.theta.core.dsl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.Stmts.*;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.dsl.gen.CoreDslBaseVisitor;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.HavocStmtContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.AssignStmtContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.AssumeStmtContext;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.TypeUtils;

public final class StmtCreatorVisitor extends CoreDslBaseVisitor<Stmt> {

	final Scope scope;

	public StmtCreatorVisitor(final Scope scope) {
		this.scope = checkNotNull(scope);
	}

	@Override
	public Stmt visitAssignStmt(final AssignStmtContext ctx) {
		@SuppressWarnings("unchecked") final VarDecl<Type> lhs = (VarDecl<Type>) resolveVar(scope, ctx.lhs.getText());
		final Expr<?> expr = CoreDslHelper.createExpr(scope, ctx.value);
		final Expr<Type> value = TypeUtils.cast(expr, lhs.getType());
		return Assign(lhs, value);
	}

	private VarDecl<?> resolveVar(final Scope scope, final String name) {
		final DeclSymbol declSymbol = CoreDslHelper.resolveDecl(scope, name);
		final Decl<?> decl = declSymbol.getDecl();
		checkArgument(decl instanceof VarDecl);
		final VarDecl<?> varDecl = (VarDecl<?>) decl;
		return varDecl;
	}

	@Override
	public AssumeStmt visitAssumeStmt(final AssumeStmtContext ctx) {
		final Expr<BoolType> cond = CoreDslHelper.createBoolExpr(scope, ctx.cond);
		return Assume(cond);
	}

	@Override
	public Stmt visitHavocStmt(final HavocStmtContext ctx) {
		@SuppressWarnings("unchecked") final VarDecl<Type> lhs = (VarDecl<Type>) resolveVar(scope, ctx.lhs.getText());
		return Havoc(lhs);
	}

}
