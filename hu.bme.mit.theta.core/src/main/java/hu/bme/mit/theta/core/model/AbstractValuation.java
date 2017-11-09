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
package hu.bme.mit.theta.core.model;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class AbstractValuation extends Valuation {

	@Override
	public final Expr<BoolType> toExpr() {
		final List<Expr<BoolType>> exprs = new ArrayList<>();
		for (final Decl<?> decl : getDecls()) {
			final Expr<BoolType> expr = Eq(decl.getRef(), eval(decl).get());
			exprs.add(expr);
		}
		return And(exprs);
	}

	@Override
	public final String toString() {
		return Utils.lispStringBuilder("").addAll(getDecls(), d -> d.getName() + " <- " + eval(d).get()).toString();
	}

}
