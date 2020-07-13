/*
 * Copyright 2019 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.dsl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.List;

import static com.google.common.base.Preconditions.checkState;

public class CallStmt extends XcfaCallStmt {
	private final VarDecl<?> var;
	private final boolean isVoid;
	private final List<VarDecl<?>> params;
	private XCFA.Process.Procedure procedure;

	public CallStmt(VarDecl<?> var, XCFA.Process.Procedure procedure, List<VarDecl<?>> params) {
		this.var = var;
		isVoid = var == null;
		this.procedure = procedure;
		this.params = params;
	}

	public boolean isVoid() {
		return isVoid;
	}

	public VarDecl<?> getVar() {
		return var;
	}

	public List<VarDecl<?>> getParams() {
		return params;
	}

	public XCFA.Process.Procedure getProcedure() {
		return procedure;
	}

	public void setProcedure(XCFA.Process.Procedure procedure) {
		checkState(this.procedure == null);
		this.procedure = procedure;
	}
}
