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

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import java.util.List;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class AndGate extends HwElement {
	private final int rhs1, rhs2;

	public AndGate(final String[] tokens) {
		this(Integer.parseInt(tokens[0]), Integer.parseInt(tokens[1]), Integer.parseInt(tokens[2]));
	}

	public AndGate(final int lhs, final int rhs1, final int rhs2) {
		super(lhs / 2);
		this.rhs1 = rhs1;
		this.rhs2 = rhs2;
	}

	@Override
	public Expr<BoolType> getExpr(final List<HwElement> elements) {
		Expr<BoolType> expr1 = elements.get(rhs1 / 2).getExpr(elements);
		if (rhs1 % 2 != 0) {
			expr1 = Not(expr1);
		}

		Expr<BoolType> expr2 = elements.get(rhs2 / 2).getExpr(elements);
		if (rhs2 % 2 != 0) {
			expr2 = Not(expr2);
		}

		return And(expr1, expr2);
	}

}
