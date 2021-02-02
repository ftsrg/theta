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
package hu.bme.mit.theta.sts.analysis;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.VarIndexing.all;

import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.sts.STS;

/**
 * Represents an action for an STS, which is simply the transition relation.
 */
public final class StsAction implements ExprAction {

	private final Expr<BoolType> trans;

	StsAction(final STS sts) {
		checkNotNull(sts);
		this.trans = sts.getTrans();
	}

	@Override
	public Expr<BoolType> toExpr() {
		return trans;
	}

	@Override
	public VarIndexing nextIndexing() {
		return all(1);
	}

	@Override
	public String toString() {
		return trans.toString();
	}
}
