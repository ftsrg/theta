package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.model.impl.Valuation;

public abstract class ExprTraceStatus2<R extends Refutation> {

	private ExprTraceStatus2() {
	}

	public static <R extends Refutation> Infeasible<R> infeasible(final R refutation) {
		return new Infeasible<>(refutation);
	}

	public static <R extends Refutation> Feasible<R> feasible(final List<Valuation> valuations) {
		return new Feasible<>(valuations);
	}

	public abstract boolean isInfeasible();

	public abstract boolean isFeasible();

	public abstract Infeasible<R> asInfeasible();

	public abstract Feasible<R> asFeasible();

	public final static class Infeasible<R extends Refutation> extends ExprTraceStatus2<R> {
		private final R refutation;

		private Infeasible(final R refutation) {
			this.refutation = checkNotNull(refutation);
		}

		public R getRefutation() {
			return refutation;
		}

		@Override
		public boolean isInfeasible() {
			return true;
		}

		@Override
		public boolean isFeasible() {
			return false;
		}

		@Override
		public Infeasible<R> asInfeasible() {
			return this;
		}

		@Override
		public Feasible<R> asFeasible() {
			throw new ClassCastException(
					"Cannot cast " + Infeasible.class.getSimpleName() + " to " + Feasible.class.getSimpleName());
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(ExprTraceStatus2.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}

	}

	public final static class Feasible<R extends Refutation> extends ExprTraceStatus2<R> {
		private final List<Valuation> valuations;

		private Feasible(final List<Valuation> valuations) {
			this.valuations = ImmutableList.copyOf(valuations);
		}

		public List<Valuation> getValuations() {
			return valuations;
		}

		@Override
		public boolean isInfeasible() {
			return false;
		}

		@Override
		public boolean isFeasible() {
			return true;
		}

		@Override
		public Infeasible<R> asInfeasible() {
			throw new ClassCastException(
					"Cannot cast " + Feasible.class.getSimpleName() + " to " + Infeasible.class.getSimpleName());
		}

		@Override
		public Feasible<R> asFeasible() {
			return this;
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(ExprTraceStatus2.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}

	}
}
