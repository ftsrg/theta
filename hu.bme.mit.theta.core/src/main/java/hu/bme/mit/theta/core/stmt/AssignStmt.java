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
package hu.bme.mit.theta.core.stmt;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class AssignStmt<DeclType extends Type> implements Stmt {

	private static final int HASH_SEED = 409;
	private static final String STMT_LABEL = "assign";

	private volatile int hashCode = 0;

	private final VarDecl<DeclType> varDecl;
	private final Expr<DeclType> expr;

	AssignStmt(final VarDecl<DeclType> varDecl, final Expr<DeclType> expr) {
		this.varDecl = checkNotNull(varDecl);
		this.expr = checkNotNull(expr);
	}

	public VarDecl<DeclType> getVarDecl() {
		return varDecl;
	}

	public Expr<DeclType> getExpr() {
		return expr;
	}

	@Override
	public <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + varDecl.hashCode();
			result = 31 * result + expr.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof AssignStmt) {
			final AssignStmt<?> that = (AssignStmt<?>) obj;
			return this.getVarDecl().equals(that.getVarDecl()) && this.getExpr().equals(that.getExpr());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(STMT_LABEL).add(varDecl.getName()).add(expr).toString();
	}
}
