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
package hu.bme.mit.theta.core.type.booltype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;

public final class FalseExpr extends BoolLitExpr {
	private static final FalseExpr INSTANCE = new FalseExpr();
	private static final int HASH_SEED = 712514;
	private static final String OPERATOR_LABEL = "false";

	private FalseExpr() {
	}

	public static FalseExpr getInstance() {
		return INSTANCE;
	}

	@Override
	public boolean getValue() {
		return false;
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public LitExpr<BoolType> eval(final Valuation val) {
		return this;
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof FalseExpr);
	}

	@Override
	public String toString() {
		return OPERATOR_LABEL;
	}

}
