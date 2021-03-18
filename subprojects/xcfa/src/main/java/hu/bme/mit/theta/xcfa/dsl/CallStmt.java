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

import hu.bme.mit.theta.common.LispStringBuilder;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.XCFAProcedure;

import java.util.List;

import static com.google.common.base.Preconditions.checkState;

//TODO: retVar not necessary, params not only variables
public class CallStmt extends XcfaCallStmt {
	private final VarDecl<?> var;
	private final List<Expr<?>> params;
	private static final String STMT_LABEL = "call";

	// not final due to circular dependency while building
	private XCFAProcedure procedure;

	public CallStmt(VarDecl<?> var, XCFAProcedure procedure, List<Expr<?>> params) {
		this.var = var;
		this.procedure = procedure;
		this.params = params;
	}

	public boolean isVoid() {
		return var == null;
	}

	public VarDecl<?> getResultVar() {
		return var;
	}

	public List<Expr<?>> getParams() {
		return params;
	}

	public XCFAProcedure getProcedure() {
		return procedure;
	}

	public void setProcedure(XCFAProcedure procedure) {
		checkState(this.procedure == null);
		this.procedure = procedure;
	}

	@Override
	public String toString() {
		LispStringBuilder call = Utils.lispStringBuilder(STMT_LABEL).add(var == null ? "void" : var.getName()).add(procedure.getName());
		for (Expr<?> param : params) {
			call.add(param);
		}
		return call.toString();
	}
}
