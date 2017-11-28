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
package hu.bme.mit.theta.core.utils;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Imply;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.BasicSubstitution;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class WpState {
	private static final int HASH_SEED = 2029;
	private volatile int hashCode = 0;

	private final Expr<BoolType> expr;
	private final int constCount;

	private WpState(final Expr<BoolType> expr, final int constCount) {
		checkNotNull(expr);
		checkArgument(constCount >= 0);
		this.expr = expr;
		this.constCount = constCount;
	}

	public static WpState of(final Expr<BoolType> expr) {
		return new WpState(expr, 0);
	}

	public Expr<BoolType> getExpr() {
		return expr;
	}

	public WpState wp(final Stmt stmt) {
		return stmt.accept(WpVisitor.getInstance(), this);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + expr.hashCode();
			result = 31 * result + constCount;
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof WpState) {
			final WpState that = (WpState) obj;
			return this.constCount == that.constCount && this.expr.equals(that.expr);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).add(expr).add(Integer.valueOf(constCount))
				.toString();
	}

	private static final class WpVisitor implements StmtVisitor<WpState, WpState> {

		private WpVisitor() {
		}

		private static class LazyHolder {
			private static final WpVisitor INSTANCE = new WpVisitor();
		}

		public static WpVisitor getInstance() {
			return LazyHolder.INSTANCE;
		}

		@Override
		public WpState visit(final SkipStmt stmt, final WpState state) {
			return state;
		}

		@Override
		public WpState visit(final AssumeStmt stmt, final WpState state) {
			final Expr<BoolType> expr = Imply(stmt.getCond(), state.getExpr());
			final int constCount = state.constCount;
			return new WpState(expr, constCount);
		}

		@Override
		public <DeclType extends Type> WpState visit(final AssignStmt<DeclType> stmt, final WpState state) {
			final VarDecl<DeclType> var = stmt.getVarDecl();
			final Substitution sub = BasicSubstitution.builder().put(var, stmt.getExpr()).build();
			final Expr<BoolType> expr = sub.apply(state.getExpr());
			final int constCount = state.constCount;
			return new WpState(expr, constCount);
		}

		@Override
		public <DeclType extends Type> WpState visit(final HavocStmt<DeclType> stmt, final WpState state) {
			final VarDecl<DeclType> var = stmt.getVarDecl();
			final int constCount = state.constCount + 1;
			final String valName = String.format("_val_%d", constCount);
			final Expr<DeclType> val = Const(valName, var.getType()).getRef();
			final Substitution sub = BasicSubstitution.builder().put(var, val).build();
			final Expr<BoolType> expr = sub.apply(state.getExpr());
			return new WpState(expr, constCount);
		}
	}
}
