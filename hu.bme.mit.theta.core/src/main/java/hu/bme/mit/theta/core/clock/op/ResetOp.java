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
package hu.bme.mit.theta.core.clock.op;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class ResetOp implements ClockOp {

	private static final int HASH_SEED = 4507;

	private final VarDecl<RatType> var;
	private final int value;

	private volatile int hashCode = 0;
	private volatile AssignStmt<RatType> stmt = null;

	ResetOp(final VarDecl<RatType> clock, final int value) {
		checkArgument(value >= 0);
		this.var = checkNotNull(clock);
		this.value = value;
	}

	public VarDecl<RatType> getVar() {
		return var;
	}

	public int getValue() {
		return value;
	}

	@Override
	public Collection<VarDecl<RatType>> getVars() {
		return ImmutableSet.of(var);
	}

	@Override
	public AssignStmt<RatType> toStmt() {
		AssignStmt<RatType> result = stmt;
		if (result == null) {
			result = Assign(var, Rat(value, 1));
			stmt = result;
		}
		return result;
	}

	@Override
	public <P, R> R accept(final ClockOpVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + var.hashCode();
			result = 31 * result + value;
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ResetOp) {
			final ResetOp that = (ResetOp) obj;
			return this.getVar().equals(that.getVar()) && this.getValue() == that.getValue();
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder("Reset").add(var.getName()).add(value).toString();
	}

}
