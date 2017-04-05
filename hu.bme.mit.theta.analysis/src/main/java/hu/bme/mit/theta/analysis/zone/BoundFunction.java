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
import hu.bme.mit.theta.formalism.ta.constr.AndConstr;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitEqConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitGeqConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitGtConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitLeqConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitLtConstr;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.utils.impl.FailClockConstrVisitor;

public final class BoundFunction {
	private static final int HASH_SEED = 2903;
	private static final BoundFunction TOP = BoundFunction.builder().build();

	private final Map<ClockDecl, Integer> clockToLower;
	private final Map<ClockDecl, Integer> clockToUpper;

	private volatile int hashCode = 0;

	private BoundFunction(final Builder builder) {
		clockToLower = builder.clockToLower;
		clockToUpper = builder.clockToUpper;
	}

	private BoundFunction(final Map<ClockDecl, Integer> clockToLower, final Map<ClockDecl, Integer> clockToUpper) {
		this.clockToLower = clockToLower;
		this.clockToUpper = clockToUpper;
	}

	public BoundFunction merge(final BoundFunction that) {
		checkNotNull(that);
		final Map<ClockDecl, Integer> clockToLower = new HashMap<>(this.clockToLower);
		final Map<ClockDecl, Integer> clockToUpper = new HashMap<>(this.clockToUpper);

		that.clockToLower.forEach((c, b) -> clockToLower.merge(c, b, Integer::max));
		that.clockToUpper.forEach((c, b) -> clockToUpper.merge(c, b, Integer::max));

		return new BoundFunction(clockToLower, clockToUpper);
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

	public Optional<Integer> getLower(final ClockDecl clock) {
		checkNotNull(clock);
		if (clock.equals(ZeroClock.getInstance())) {
			return Optional.of(0);
		} else {
			return Optional.ofNullable(clockToLower.get(clock));
		}
	}

	public Optional<Integer> getUpper(final ClockDecl clock) {
		checkNotNull(clock);
		if (clock.equals(ZeroClock.getInstance())) {
			return Optional.of(0);
		} else {
			return Optional.ofNullable(clockToUpper.get(clock));
		}
	}

	public Collection<ClockDecl> getLowerClocks() {
		return Collections.unmodifiableCollection(clockToLower.keySet());
	}

	public Collection<ClockDecl> getUpperClocks() {
		return Collections.unmodifiableCollection(clockToUpper.keySet());
	}

	public boolean isLeq(final BoundFunction that) {
		checkNotNull(that);
		return isLeq(this.clockToLower, that.clockToLower) && isLeq(this.clockToUpper, that.clockToUpper);
	}

	private static boolean isLeq(final Map<ClockDecl, Integer> map1, final Map<ClockDecl, Integer> map2) {
		return map1.entrySet().stream()
				.allMatch(e1 -> map2.containsKey(e1.getKey()) && e1.getValue() <= map2.get(e1.getKey()));
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + clockToLower.hashCode();
			result = 31 * result + clockToUpper.hashCode();
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
			return this.clockToLower.equals(that.clockToLower) && this.clockToUpper.equals(that.clockToUpper);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final String lowerToString = ObjectUtils.toStringBuilder("L").addAll(clockToLower.entrySet().stream()
				.map(e -> e.getKey().getName() + " <- " + e.getValue()).collect(toList())).toString();

		final String UpperToString = ObjectUtils.toStringBuilder("U").addAll(clockToUpper.entrySet().stream()
				.map(e -> e.getKey().getName() + " <- " + e.getValue()).collect(toList())).toString();

		return ObjectUtils.toStringBuilder(this.getClass().getSimpleName()).add(lowerToString).add(UpperToString)
				.toString();
	}

	public static final class Builder {
		private volatile BoundFunction boundFunction;
		private final Map<ClockDecl, Integer> clockToLower;
		private final Map<ClockDecl, Integer> clockToUpper;

		private Builder() {
			this.boundFunction = null;
			this.clockToLower = new HashMap<>();
			this.clockToUpper = new HashMap<>();
		}

		private Builder(final BoundFunction boundFunction) {
			this.boundFunction = null;
			this.clockToLower = new HashMap<>(boundFunction.clockToLower);
			this.clockToUpper = new HashMap<>(boundFunction.clockToUpper);
		}

		public Builder remove(final ClockDecl clock) {
			checkState(!isBuilt());
			clockToLower.remove(clock);
			clockToUpper.remove(clock);
			return this;
		}

		public Builder add(final ClockConstr constr) {
			checkState(!isBuilt());
			constr.accept(BoundFunctionClockConstrVisitor.INSTANCE, this);
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

	private static final class BoundFunctionClockConstrVisitor extends FailClockConstrVisitor<Builder, Void> {
		private static final BoundFunctionClockConstrVisitor INSTANCE = new BoundFunctionClockConstrVisitor();

		private BoundFunctionClockConstrVisitor() {
		}

		@Override
		public Void visit(final UnitLtConstr constr, final Builder builder) {
			final ClockDecl clock = constr.getClock();
			final int bound = constr.getBound();
			builder.clockToUpper.merge(clock, bound, Integer::max);
			return null;
		}

		@Override
		public Void visit(final UnitLeqConstr constr, final Builder builder) {
			final ClockDecl clock = constr.getClock();
			final int bound = constr.getBound();
			builder.clockToUpper.merge(clock, bound, Integer::max);
			return null;
		}

		@Override
		public Void visit(final UnitGtConstr constr, final Builder builder) {
			final ClockDecl clock = constr.getClock();
			final int bound = constr.getBound();
			builder.clockToLower.merge(clock, bound, Integer::max);
			return null;
		}

		@Override
		public Void visit(final UnitGeqConstr constr, final Builder builder) {
			final ClockDecl clock = constr.getClock();
			final int bound = constr.getBound();
			builder.clockToLower.merge(clock, bound, Integer::max);
			return null;
		}

		@Override
		public Void visit(final UnitEqConstr constr, final Builder builder) {
			final ClockDecl clock = constr.getClock();
			final int bound = constr.getBound();
			builder.clockToLower.merge(clock, bound, Integer::max);
			builder.clockToUpper.merge(clock, bound, Integer::max);
			return null;
		}

		@Override
		public Void visit(final AndConstr constr, final Builder builder) {
			constr.getConstrs().forEach(c -> c.accept(this, builder));
			return null;
		}
	}

}
