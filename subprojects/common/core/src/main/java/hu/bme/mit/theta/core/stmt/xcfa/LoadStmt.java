/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.core.stmt.xcfa;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.stmt.XcfaStmt;

public class LoadStmt extends XcfaStmt {
	private final VarDecl<?> lhs;
	private final VarDecl<?> rhs;
	private final boolean atomic;
	private final String ordering;


	private static final int HASH_SEED = 415;
	private static final String STMT_LABEL = "load";

	private volatile int hashCode = 0;

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + lhs.hashCode();
			result = 31 * result + rhs.hashCode();
			result = 31 * result + (atomic ? 1 : 0) ;
			result = 31 * result + ordering.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj instanceof LoadStmt
				&& ((LoadStmt) obj).getLhs().equals(lhs)
				&& ((LoadStmt) obj).getRhs().equals(rhs)
				&& ((LoadStmt) obj).getOrdering().equals(ordering)
				&& ((LoadStmt) obj).isAtomic() == atomic;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(STMT_LABEL).add(lhs).add(rhs).add(atomic).add(ordering).toString();
	}
	public LoadStmt(VarDecl<?> lhs, VarDecl<?> rhs, boolean atomic, String ordering) {
		this.lhs = lhs;
		this.rhs = rhs;
		this.atomic = atomic;
		this.ordering = ordering;
	}

	@Override
	public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}

	@Override
	public <P, R> R accept(XcfaStmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}

	public VarDecl<?> getLhs() {
		return lhs;
	}

	public VarDecl<?> getRhs() {
		return rhs;
	}

	public boolean isAtomic() {
		return atomic;
	}

	public String getOrdering() {
		return ordering;
	}
}
