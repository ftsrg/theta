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

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static java.util.stream.Collectors.toSet;

import java.util.Collection;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class AndConstr implements ClockConstr {

	private static final int HASH_SEED = 6133;

	private final Collection<? extends AtomicConstr> constrs;

	private volatile int hashCode = 0;
	private volatile AndExpr expr = null;

	AndConstr(final Collection<? extends ClockConstr> constrs) {
		checkNotNull(constrs);
		this.constrs = toAtomicConstrs(constrs);
	}

	public Collection<? extends AtomicConstr> getConstrs() {
		return constrs;
	}

	@Override
	public Collection<VarDecl<RatType>> getVars() {
		final ImmutableSet.Builder<VarDecl<RatType>> builder = ImmutableSet.builder();
		for (final ClockConstr constr : constrs) {
			builder.addAll(constr.getVars());
		}
		return builder.build();
	}

	@Override
	public AndExpr toExpr() {
		AndExpr result = expr;
		if (result == null) {
			result = And(constrs.stream().map(ClockConstr::toExpr).collect(toSet()));
			expr = result;
		}
		return result;
	}

	@Override
	public <P, R> R accept(final ClockConstrVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + constrs.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof AndConstr) {
			final AndConstr that = (AndConstr) obj;
			return this.getConstrs().equals(that.getConstrs());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(" and ");
		constrs.forEach(c -> sj.add(c.toString()));
		return sj.toString();
	}

	////////

	private static Collection<AtomicConstr> toAtomicConstrs(final Collection<? extends ClockConstr> constrs) {
		final ImmutableSet.Builder<AtomicConstr> builder = ImmutableSet.builder();
		for (final ClockConstr constr : constrs) {
			if (constr instanceof AtomicConstr) {
				builder.add((AtomicConstr) constr);
			} else if (constr instanceof AndConstr) {
				builder.addAll(((AndConstr) constr).getConstrs());
			} else if (constr instanceof TrueConstr) {
				continue;
			} else {
				throw new AssertionError();
			}
		}
		return builder.build();
	}

}
