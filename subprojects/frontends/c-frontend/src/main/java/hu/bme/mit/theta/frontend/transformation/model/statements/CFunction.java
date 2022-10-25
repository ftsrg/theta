/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;

import java.util.List;

public class CFunction extends CStatement {
	private final CDeclaration funcDecl;
	private final CStatement compound;
	private final List<VarDecl<?>> flatVariables;

	public CFunction(CDeclaration funcDecl, CStatement compound, List<VarDecl<?>> flatVariables) {
		this.funcDecl = funcDecl;
		this.compound = compound;
		this.flatVariables = flatVariables;
		FrontendMetadata.lookupMetadata(funcDecl).forEach((s, o) -> FrontendMetadata.create(this, s, o));
	}

	public CStatement getCompound() {
		return compound;
	}

	public CDeclaration getFuncDecl() {
		return funcDecl;
	}

	public List<VarDecl<?>> getFlatVariables() {
		return flatVariables;
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
