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

import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.utils.StmtVisitor;

public final class BlockStmt implements Stmt {

	private static final int HASH_SEED = 757;
	private volatile int hashCode = 0;

	private final List<? extends Stmt> stmts;

	BlockStmt(final List<? extends Stmt> stmts) {
		this.stmts = ImmutableList.copyOf(checkNotNull(stmts));
	}

	public List<? extends Stmt> getStmts() {
		return stmts;
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
			result = 31 * result + stmts.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof BlockStmt) {
			final BlockStmt that = (BlockStmt) obj;
			return this.getStmts().equals(that.getStmts());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "Block(", ")");
		for (final Stmt stmt : stmts) {
			sj.add(stmt.toString());
		}
		return sj.toString();
	}

}
