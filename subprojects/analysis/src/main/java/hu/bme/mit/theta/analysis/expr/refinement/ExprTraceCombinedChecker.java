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

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;

public final class ExprTraceCombinedChecker<R extends Refutation> implements ExprTraceChecker<R> {

	private final Collection<ExprTraceChecker<R>> checkers;
	private final ExprTraceStatusMerger<R> merger;

	private ExprTraceCombinedChecker(final Collection<ExprTraceChecker<R>> checkers,
			final ExprTraceStatusMerger<R> merger) {
		this.checkers = ImmutableList.copyOf(checkNotNull(checkers));
		this.merger = checkNotNull(merger);
	}

	public static <R extends Refutation> ExprTraceCombinedChecker<R> create(final ExprTraceChecker<R> checker1,
			final ExprTraceChecker<R> checker2, final ExprTraceStatusMerger<R> merger) {
		return new ExprTraceCombinedChecker<>(ImmutableList.of(checker1, checker2), merger);
	}

	@Override
	public ExprTraceStatus<R> check(final Trace<? extends ExprState, ? extends ExprAction> trace) {
		final List<ExprTraceStatus<R>> statuses = checkers.stream().map(c -> c.check(trace))
				.collect(Collectors.toList());
		return merger.merge(statuses);
	}
}
