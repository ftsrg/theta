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
package hu.bme.mit.theta.analysis.expr.refinement;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;

public abstract class ExprTraceStatus<R extends Refutation> {

	private ExprTraceStatus() {
	}

	public static <R extends Refutation> Infeasible<R> infeasible(final R refutation) {
		return new Infeasible<>(refutation);
	}

	public static <R extends Refutation> Feasible<R> feasible(final Trace<Valuation, ? extends Action> valuations) {
		return new Feasible<>(valuations);
	}

	public abstract boolean isInfeasible();

	public abstract boolean isFeasible();

	public abstract Infeasible<R> asInfeasible();

	public abstract Feasible<R> asFeasible();

	public final static class Infeasible<R extends Refutation> extends ExprTraceStatus<R> {
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
			return Utils.lispStringBuilder(ExprTraceStatus.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}

	}

	public final static class Feasible<R extends Refutation> extends ExprTraceStatus<R> {
		private final Trace<Valuation, ? extends Action> valuations;

		private Feasible(final Trace<Valuation, ? extends Action> valuations) {
			this.valuations = valuations;
		}

		public Trace<Valuation, ? extends Action> getValuations() {
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
			return Utils.lispStringBuilder(ExprTraceStatus.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}

	}
}
