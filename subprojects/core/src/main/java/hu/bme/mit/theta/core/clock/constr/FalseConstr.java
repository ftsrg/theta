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
package hu.bme.mit.theta.core.clock.constr;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class FalseConstr implements ClockConstr {

	private static final int HASH_SEED = 242101;

	private static final String CC_LABEL = "false";

	@Override
	public Collection<VarDecl<RatType>> getVars() {
		return ImmutableSet.of();
	}

	@Override
	public FalseExpr toExpr() {
		return False();
	}

	@Override
	public <P, R> R accept(final ClockConstrVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj instanceof FalseConstr;
	}

	@Override
	public String toString() {
		return CC_LABEL;
	}
}
