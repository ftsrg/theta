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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

/**
 * Assume statement of the form [EXPRESSION], where EXPRESSION is a Boolean {@link Expr}.
 * The statement is a guard that can only be passed if EXPRESSION evaluates to true.
 */
public final class AssumeStmt implements Stmt {

	private static final int HASH_SEED = 547;
	private static final String STMT_LABEL = "assume";

	private final Expr<BoolType> cond;

	private volatile int hashCode = 0;

	private AssumeStmt(final Expr<BoolType> cond) {
		this.cond = checkNotNull(cond);
	}

	public static AssumeStmt of(final Expr<BoolType> cond) {
		return new AssumeStmt(cond);
	}

	public static AssumeStmt create(final Expr<?> cond) {
		final Expr<BoolType> newCond = cast(cond, Bool());
		return AssumeStmt.of(newCond);
	}

	public Expr<BoolType> getCond() {
		return cond;
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
			result = 31 * result + cond.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof AssumeStmt) {
			final AssumeStmt that = (AssumeStmt) obj;
			return this.getCond().equals(that.getCond());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(STMT_LABEL).add(cond).toString();
	}
}
