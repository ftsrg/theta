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

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Pop statement of the form pop VARIABLE, which pops the last form of the variable from stack
 * @param <DeclType>
 */
public final class PopStmt<DeclType extends Type> implements Stmt {

	private static final int HASH_SEED = 931;
	private static final String STMT_LABEL = "pop";

	private final VarDecl<DeclType> varDecl;

	private volatile int hashCode = 0;

	private PopStmt(final VarDecl<DeclType> varDecl) {
		this.varDecl = checkNotNull(varDecl);
	}

	public static <DeclType extends Type> PopStmt<DeclType> of(final VarDecl<DeclType> varDecl) {
		return new PopStmt<>(varDecl);
	}

	public VarDecl<DeclType> getVarDecl() {
		return varDecl;
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
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof PopStmt<?>) {
			final PopStmt<?> that = (PopStmt<?>) obj;
			return this.getVarDecl().equals(that.getVarDecl());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(STMT_LABEL).add(varDecl.getName()).toString();
	}
}
