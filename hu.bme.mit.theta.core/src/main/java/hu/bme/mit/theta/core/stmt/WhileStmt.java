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
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public final class WhileStmt implements Stmt {

	private final static int HASH_SEED = 631;
	private volatile int hashCode = 0;

	private final Expr<BoolType> cond;
	private final Stmt doStmt;

	WhileStmt(final Expr<BoolType> cond, final Stmt doStmt) {
		this.cond = checkNotNull(cond);
		this.doStmt = checkNotNull(doStmt);
	}

	public Expr<BoolType> getCond() {
		return cond;
	}

	public Stmt getDo() {
		return doStmt;
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
			result = 31 * result + doStmt.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof WhileStmt) {
			final WhileStmt that = (WhileStmt) obj;
			return this.getCond().equals(that.getCond()) && this.getDo().equals(that.getDo());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder("While").add(cond).add(doStmt).toString();
	}
}
