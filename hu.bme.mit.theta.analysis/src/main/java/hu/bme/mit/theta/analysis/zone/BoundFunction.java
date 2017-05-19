package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.ta.constr.AndConstr;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.theta.formalism.ta.constr.FailClockConstrVisitor;
import hu.bme.mit.theta.formalism.ta.constr.UnitEqConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitGeqConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitGtConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitLeqConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitLtConstr;

public final class BoundFunction {
	private static final int HASH_SEED = 2903;
	private static final BoundFunction TOP = BoundFunction.builder().build();

	private final Map<VarDecl<RatType>, Integer> varToLower;
	private final Map<VarDecl<RatType>, Integer> varToUpper;

	private volatile int hashCode = 0;

	private BoundFunction(final Builder builder) {
		varToLower = builder.varToLower;
		varToUpper = builder.varToUpper;
	}

	private BoundFunction(final Map<VarDecl<RatType>, Integer> varToLower,
			final Map<VarDecl<RatType>, Integer> varToUpper) {
		this.varToLower = varToLower;
		this.varToUpper = varToUpper;
	}

	public BoundFunction merge(final BoundFunction that) {
		checkNotNull(that);
		final Map<VarDecl<RatType>, Integer> varToLower = new HashMap<>(this.varToLower);
		final Map<VarDecl<RatType>, Integer> varToUpper = new HashMap<>(this.varToUpper);

		that.varToLower.forEach((c, b) -> varToLower.merge(c, b, Integer::max));
		that.varToUpper.forEach((c, b) -> varToUpper.merge(c, b, Integer::max));

		return new BoundFunction(varToLower, varToUpper);
	}

	public static BoundFunction top() {
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

	public boolean isLeq(final BoundFunction that) {
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
		} else if (obj instanceof BoundFunction) {
			final BoundFunction that = (BoundFunction) obj;
			return this.varToLower.equals(that.varToLower) && this.varToUpper.equals(that.varToUpper);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final String lowerToString = ObjectUtils.toStringBuilder("L").addAll(
				varToLower.entrySet().stream().map(e -> e.getKey().getName() + " <- " + e.getValue()).collect(toList()))
				.toString();

		final String UpperToString = ObjectUtils.toStringBuilder("U").addAll(
				varToUpper.entrySet().stream().map(e -> e.getKey().getName() + " <- " + e.getValue()).collect(toList()))
				.toString();

		return ObjectUtils.toStringBuilder(this.getClass().getSimpleName()).add(lowerToString).add(UpperToString)
				.toString();
	}

	public static final class Builder {
		private volatile BoundFunction boundFunction;
		private final Map<VarDecl<RatType>, Integer> varToLower;
		private final Map<VarDecl<RatType>, Integer> varToUpper;

		private Builder() {
			this.boundFunction = null;
			this.varToLower = new HashMap<>();
			this.varToUpper = new HashMap<>();
		}

		private Builder(final BoundFunction boundFunction) {
			this.boundFunction = null;
			this.varToLower = new HashMap<>(boundFunction.varToLower);
			this.varToUpper = new HashMap<>(boundFunction.varToUpper);
		}

		public Builder remove(final VarDecl<RatType> var) {
			checkState(!isBuilt());
			varToLower.remove(var);
			varToUpper.remove(var);
			return this;
		}

		public Builder add(final ClockConstr constr) {
			checkState(!isBuilt());
			constr.accept(BoundFunctionVarConstrVisitor.INSTANCE, this);
			return this;
		}

		public BoundFunction build() {
			BoundFunction result = boundFunction;
			if (result == null) {
				result = new BoundFunction(this);
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
