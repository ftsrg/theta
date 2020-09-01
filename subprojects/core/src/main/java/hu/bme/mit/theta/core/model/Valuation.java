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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;

/**
 * Interface for a valuation, which is a mapping from declarations to literal expressions.
 */
public abstract class Valuation implements Substitution {
	private static final int HASH_SEED = 2141;

	@Override
	public abstract <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl);

	public abstract Map<Decl<?>, LitExpr<?>> toMap();

	/**
	 * Convert a valuation into an expression. For example if the valuation assigns
	 * 1 to x and 2 to y, the expression is (x == 1 and y == 2).
	 * @return
	 */
	public Expr<BoolType> toExpr() {
		final List<Expr<BoolType>> exprs = new ArrayList<>();
		for (final Decl<?> decl : getDecls()) {
			final Expr<BoolType> expr = Eq(decl.getRef(), eval(decl).get());
			exprs.add(expr);
		}
		return SmartBoolExprs.And(exprs);
	}

	/**
	 * Checks if an other valuation is more general than the current one. This holds
	 * if the other valuation has the same or less declarations, and for each declaration,
	 * the assigned value is the same.
	 * @param that
	 * @return
	 */
	public boolean isLeq(final Valuation that) {
		if (that.getDecls().size() > this.getDecls().size()) {
			return false;
		}
		for (final Decl<?> varDecl : that.getDecls()) {
			if (!that.eval(varDecl).equals(this.eval(varDecl))) {
				return false;
			}
		}
		return true;
	}

	@Override
	public final int hashCode() {
		return HASH_SEED * 31 + toMap().hashCode();
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof Valuation) {
			final Valuation that = (Valuation) obj;
			return this.toMap().equals(that.toMap());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder("val").aligned()
				.addAll(getDecls().stream().map(d -> String.format("(%s %s)", d.getName(), eval(d).get()))).toString();
	}

}
