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
package hu.bme.mit.theta.formalism.sts.aiger.elements;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import java.util.List;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class InVar extends HwElement {
	private final VarDecl<BoolType> varDecl;

	public InVar(final int nr, final String token) {
		this(nr, Integer.parseInt(token));
	}

	public InVar(final int nr, final int literal) {
		super(literal / 2);
		varDecl = Decls.Var("I" + nr + "_l" + varId, Bool());
	}

	@Override
	public Expr<BoolType> getExpr(final List<HwElement> elements) {
		return varDecl.getRef();
	}

}
