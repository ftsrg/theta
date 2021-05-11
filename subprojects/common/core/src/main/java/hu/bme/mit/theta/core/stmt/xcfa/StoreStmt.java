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

public class StoreStmt extends XcfaStmt {
	private final VarDecl<?> local;
	private final VarDecl<?> global;
	private final boolean atomic;
	private final String ordering;

	private static final int HASH_SEED = 416;
	private static final String STMT_LABEL = "store";

	private volatile int hashCode = 0;

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + local.hashCode();
			result = 31 * result + global.hashCode();
			result = 31 * result + (atomic ? 1 : 0) ;
			result = 31 * result + ordering.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj instanceof StoreStmt
				&& ((StoreStmt) obj).getLocal().equals(local)
				&& ((StoreStmt) obj).getGlobal().equals(global)
				&& ((StoreStmt) obj).getOrdering().equals(ordering)
				&& ((StoreStmt) obj).isAtomic() == atomic;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(STMT_LABEL).add(local).add(global).add(atomic).add(ordering).toString();
	}
	public StoreStmt(VarDecl<?> local, VarDecl<?> global, boolean atomic, String ordering) {
		this.local = local;
		this.global = global;
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

	public VarDecl<?> getLocal() {
		return local;
	}

	public VarDecl<?> getGlobal() {
		return global;
	}

	public boolean isAtomic() {
		return atomic;
	}

	public String getOrdering() {
		return ordering;
	}
}
