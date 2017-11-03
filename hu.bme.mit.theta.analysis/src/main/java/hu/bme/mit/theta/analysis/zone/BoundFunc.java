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
package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.clock.constr.AndConstr;
import hu.bme.mit.theta.core.clock.constr.ClockConstr;
import hu.bme.mit.theta.core.clock.constr.FailClockConstrVisitor;
import hu.bme.mit.theta.core.clock.constr.UnitEqConstr;
import hu.bme.mit.theta.core.clock.constr.UnitGeqConstr;
import hu.bme.mit.theta.core.clock.constr.UnitGtConstr;
import hu.bme.mit.theta.core.clock.constr.UnitLeqConstr;
import hu.bme.mit.theta.core.clock.constr.UnitLtConstr;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class BoundFunc {
	private static final int HASH_SEED = 2903;
	private static final BoundFunc TOP = BoundFunc.builder().build();

	private final Map<VarDecl<RatType>, Integer> varToLower;
	private final Map<VarDecl<RatType>, Integer> varToUpper;

	private volatile int hashCode = 0;

	private BoundFunc(final Builder builder) {
		varToLower = builder.varToLower;
		varToUpper = builder.varToUpper;
	}

	private BoundFunc(final Map<VarDecl<RatType>, Integer> varToLower,
			final Map<VarDecl<RatType>, Integer> varToUpper) {
		this.varToLower = varToLower;
		this.varToUpper = varToUpper;
	}

	public BoundFunc merge(final BoundFunc that) {
		checkNotNull(that);
		final Map<VarDecl<RatType>, Integer> varToLower = new HashMap<>(this.varToLower);
		final Map<VarDecl<RatType>, Integer> varToUpper = new HashMap<>(this.varToUpper);

		that.varToLower.forEach((c, b) -> varToLower.merge(c, b, Integer::max));
		that.varToUpper.forEach((c, b) -> varToUpper.merge(c, b, Integer::max));

		return new BoundFunc(varToLower, varToUpper);
	}

	public static BoundFunc top() {
		return TOP;
	}

	public static Builder builder() {
		return new Builder();
	}

	public Builder transform() {
		return new Builder(this);
	}

	public Optional<Integer> getLower(final VarDecl<RatType> var) {
		checkNotNull(var);
		if (var.equals(ZeroVar.getInstance())) {
			return Optional.of(0);
		} else {
			return Optional.ofNullable(varToLower.get(var));
		}
	}

	public Optional<Integer> getUpper(final VarDecl<RatType> var) {
		checkNotNull(var);
		if (var.equals(ZeroVar.getInstance())) {
			return Optional.of(0);
		} else {
			return Optional.ofNullable(varToUpper.get(var));
		}
	}

	public Collection<VarDecl<RatType>> getLowerVars() {
		return Collections.unmodifiableCollection(varToLower.keySet());
	}

	public Collection<VarDecl<RatType>> getUpperVars() {
		return Collections.unmodifiableCollection(varToUpper.keySet());
	}

	public boolean isLeq(final BoundFunc that) {
		checkNotNull(that);
		return isLeq(this.varToLower, that.varToLower) && isLeq(this.varToUpper, that.varToUpper);
	}

	private static boolean isLeq(final Map<VarDecl<RatType>, Integer> map1, final Map<VarDecl<RatType>, Integer> map2) {
		return map1.entrySet().stream()
				.allMatch(e1 -> map2.containsKey(e1.getKey()) && e1.getValue() <= map2.get(e1.getKey()));
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + varToLower.hashCode();
			result = 31 * result + varToUpper.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof BoundFunc) {
			final BoundFunc that = (BoundFunc) obj;
			return this.varToLower.equals(that.varToLower) && this.varToUpper.equals(that.varToUpper);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final String lowerToString = Utils.lispStringBuilder("L").addAll(
				varToLower.entrySet().stream().map(e -> e.getKey().getName() + " <- " + e.getValue()).collect(toList()))
				.toString();

		final String UpperToString = Utils.lispStringBuilder("U").addAll(
				varToUpper.entrySet().stream().map(e -> e.getKey().getName() + " <- " + e.getValue()).collect(toList()))
				.toString();

		return Utils.lispStringBuilder(this.getClass().getSimpleName()).add(lowerToString).add(UpperToString).toString();
	}

	public static final class Builder {
		private volatile BoundFunc boundFunction;
		private final Map<VarDecl<RatType>, Integer> varToLower;
		private final Map<VarDecl<RatType>, Integer> varToUpper;

		private Builder() {
			this.boundFunction = null;
			this.varToLower = new HashMap<>();
			this.varToUpper = new HashMap<>();
		}

		private Builder(final BoundFunc boundFunction) {
			this.boundFunction = null;
			this.varToLower = new HashMap<>(boundFunction.varToLower);
			this.varToUpper = new HashMap<>(boundFunction.varToUpper);
		}

		public Builder remove(final VarDecl<RatType> var) {
			checkState(!isBuilt(), "Already built.");
			varToLower.remove(var);
			varToUpper.remove(var);
			return this;
		}

		public Builder add(final ClockConstr constr) {
			checkState(!isBuilt(), "Already built.");
			constr.accept(BoundFunctionVarConstrVisitor.INSTANCE, this);
			return this;
		}

		public BoundFunc build() {
			BoundFunc result = boundFunction;
			if (result == null) {
				result = new BoundFunc(this);
				boundFunction = result;
			}
			return result;
		}

		private boolean isBuilt() {
			return boundFunction != null;
		}
	}

	private static final class BoundFunctionVarConstrVisitor extends FailClockConstrVisitor<Builder, Void> {
		private static final BoundFunctionVarConstrVisitor INSTANCE = new BoundFunctionVarConstrVisitor();

		private BoundFunctionVarConstrVisitor() {
		}

		@Override
		public Void visit(final UnitLtConstr constr, final Builder builder) {
			final VarDecl<RatType> var = constr.getVar();
			final int bound = constr.getBound();
			builder.varToUpper.merge(var, bound, Integer::max);
			return null;
		}

		@Override
		public Void visit(final UnitLeqConstr constr, final Builder builder) {
			final VarDecl<RatType> var = constr.getVar();
			final int bound = constr.getBound();
			builder.varToUpper.merge(var, bound, Integer::max);
			return null;
		}

		@Override
		public Void visit(final UnitGtConstr constr, final Builder builder) {
			final VarDecl<RatType> var = constr.getVar();
			final int bound = constr.getBound();
			builder.varToLower.merge(var, bound, Integer::max);
			return null;
		}

		@Override
		public Void visit(final UnitGeqConstr constr, final Builder builder) {
			final VarDecl<RatType> var = constr.getVar();
			final int bound = constr.getBound();
			builder.varToLower.merge(var, bound, Integer::max);
			return null;
		}

		@Override
		public Void visit(final UnitEqConstr constr, final Builder builder) {
			final VarDecl<RatType> var = constr.getVar();
			final int bound = constr.getBound();
			builder.varToLower.merge(var, bound, Integer::max);
			builder.varToUpper.merge(var, bound, Integer::max);
			return null;
		}

		@Override
		public Void visit(final AndConstr constr, final Builder builder) {
			constr.getConstrs().forEach(c -> c.accept(this, builder));
			return null;
		}
	}

}
