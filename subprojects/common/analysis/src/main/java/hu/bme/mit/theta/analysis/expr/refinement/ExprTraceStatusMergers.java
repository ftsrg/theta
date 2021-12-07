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

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;

public final class ExprTraceStatusMergers {

	private ExprTraceStatusMergers() {
	}

	public static <R extends Refutation> ExprTraceStatusMerger<R> minPruneIndex() {
		return new MinPruneIndex<>();
	}

	public static <R extends Refutation> ExprTraceStatusMerger<R> maxPruneIndex() {
		return new MaxPruneIndex<>();
	}

	private static class MinPruneIndex<R extends Refutation> implements ExprTraceStatusMerger<R> {
		@Override
		public ExprTraceStatus<R> merge(final Collection<ExprTraceStatus<R>> statuses) {
			checkArgument(!statuses.isEmpty(), "No statuses to merge.");

			final ExprTraceStatus<R> firstStatus = statuses.iterator().next();
			if (firstStatus.isFeasible()) {
				assert statuses.stream().allMatch(ExprTraceStatus::isFeasible);
				return firstStatus;
			} else {
				assert statuses.stream().allMatch(ExprTraceStatus::isInfeasible);
				return statuses.stream().map(ExprTraceStatus::asInfeasible).min((s1, s2) -> Integer
						.compare(s1.getRefutation().getPruneIndex(), s2.getRefutation().getPruneIndex())).get();
			}
		}
	}

	private static class MaxPruneIndex<R extends Refutation> implements ExprTraceStatusMerger<R> {
		@Override
		public ExprTraceStatus<R> merge(final Collection<ExprTraceStatus<R>> statuses) {
			checkArgument(!statuses.isEmpty(), "No statuses to merge.");

			final ExprTraceStatus<R> firstStatus = statuses.iterator().next();
			if (firstStatus.isFeasible()) {
				assert statuses.stream().allMatch(ExprTraceStatus::isFeasible);
				return firstStatus;
			} else {
				assert statuses.stream().allMatch(ExprTraceStatus::isInfeasible);
				return statuses.stream().map(ExprTraceStatus::asInfeasible).max((s1, s2) -> Integer
						.compare(s1.getRefutation().getPruneIndex(), s2.getRefutation().getPruneIndex())).get();
			}
		}
	}
}
