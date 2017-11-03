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

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class FreeOp implements ClockOp {

	private static final int HASH_SEED = 2281;

	private final VarDecl<RatType> var;

	private volatile int hashCode = 0;
	private volatile HavocStmt<RatType> stmt = null;

	FreeOp(final VarDecl<RatType> var) {
		this.var = checkNotNull(var);
	}

	public VarDecl<RatType> getVar() {
		return var;
	}

	@Override
	public Collection<VarDecl<RatType>> getVars() {
		return ImmutableSet.of(var);
	}

	@Override
	public HavocStmt<RatType> toStmt() {
		HavocStmt<RatType> result = stmt;
		if (result == null) {
			result = Havoc(var);
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
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FreeOp) {
			final FreeOp that = (FreeOp) obj;
			return this.getVar().equals(that.getVar());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder("Free").add(var.getName()).toString();
	}

}
