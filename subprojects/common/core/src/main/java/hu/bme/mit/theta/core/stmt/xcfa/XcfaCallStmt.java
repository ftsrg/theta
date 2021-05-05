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

import hu.bme.mit.theta.common.LispStringBuilder;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.type.Expr;

import java.util.List;

public class XcfaCallStmt extends XcfaStmt {
	private static final String STMT_LABEL = "call";
	private final List<Expr<?>> params;
	private final String procedure;

	private static final int HASH_SEED = 417;

	private volatile int hashCode = 0;

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + params.hashCode();
			result = 31 * result + procedure.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj instanceof XcfaCallStmt
				&& ((XcfaCallStmt) obj).getParams().equals(params)
				&& ((XcfaCallStmt) obj).getProcedure().equals(procedure);
	}

	public XcfaCallStmt(List<Expr<?>> params, String procedure) {
		this.params = params;
		this.procedure = procedure;
	}

	@Override
	public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}

	@Override
	public <P, R> R accept(XcfaStmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}

	public List<Expr<?>> getParams() {
		return params;
	}

	public String getProcedure() {
		return procedure;
	}

	public XcfaCallStmt of(List<Expr<?>> params, String procedure) {
		return new XcfaCallStmt(params, procedure);
	}

	@Override
	public String toString() {
		LispStringBuilder call = Utils.lispStringBuilder(STMT_LABEL).add(procedure);
		params.forEach(expr ->
			call.add(Utils.lispStringBuilder().add(expr)));
		return call.toString();
	}
}
