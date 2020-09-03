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

/**
 * A skip statement is a placeholder that does not perform any operation.
 */
public final class SkipStmt implements Stmt {

	private static final int HASH_CODE = 1310147;
	private static final String STMT_LABEL = "skip";

	private SkipStmt() {
	}

	private static class LazyHolder {
		static final SkipStmt INSTANCE = new SkipStmt();
	}

	public static SkipStmt getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		return HASH_CODE;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else {
			return this.getClass() == obj.getClass();
		}
	}

	@Override
	public String toString() {
		return STMT_LABEL;
	}

}
