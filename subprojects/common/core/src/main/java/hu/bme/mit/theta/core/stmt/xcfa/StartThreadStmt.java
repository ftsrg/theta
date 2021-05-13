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
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.type.Expr;

public class StartThreadStmt extends XcfaStmt {
	private final String key;
	private final String threadName;
	private final Expr<?> param;


	private static final int HASH_SEED = 414;
	private static final String STMT_LABEL = "start-thread";

	private volatile int hashCode = 0;

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + key.hashCode();
			result = 31 * result + threadName.hashCode();
			result = 31 * result + param.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj instanceof StartThreadStmt
				&& ((StartThreadStmt) obj).getKey().equals(key)
				&& ((StartThreadStmt) obj).getThreadName().equals(threadName)
				&& ((StartThreadStmt) obj).getParam().equals(param);
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(STMT_LABEL).add(key).add(threadName).add(param == null ? "" : param).toString();
	}

	public StartThreadStmt(String key, String threadName, Expr<?> param) {
		this.key = key;
		this.threadName = threadName;
		this.param = param;
	}

	@Override
	public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}

	@Override
	public <P, R> R accept(XcfaStmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}

	public String getThreadName() {
		return threadName;
	}

	public Expr<?> getParam() {
		return param;
	}

	public String getKey() {
		return key;
	}
}
