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

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import java.util.List;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class OutVar extends HwElement {
	private final int literal;

	public OutVar(final String token) {
		this(Integer.parseInt(token));
	}

	public OutVar(final int literal) {
		super(-1);
		this.literal = literal;
	}

	@Override
	public Expr<BoolType> getExpr(final List<HwElement> elements) {
		Expr<BoolType> expr = elements.get(literal / 2).getExpr(elements);
		if (literal % 2 != 0) {
			expr = Not(expr);
		}
		return expr;
	}

	@Override
	public int getVarId() {
		throw new UnsupportedOperationException("OutVars do not have corresponding ID.");
	}

}
