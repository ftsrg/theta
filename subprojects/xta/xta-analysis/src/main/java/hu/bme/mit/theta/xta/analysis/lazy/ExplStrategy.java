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
package hu.bme.mit.theta.xta.analysis.lazy;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplAnalysis;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics.Builder;

final class ExplStrategy<S extends State> implements AlgorithmStrategy<S, ExplState> {

	private final Lens<S, ExplState> lens;
	private final Analysis<ExplState, XtaAction, UnitPrec> analysis;
	private final Function<ExplState, ?> projection;

	public ExplStrategy(final XtaSystem system, final Lens<S, ExplState> lens) {
		checkNotNull(system);
		this.lens = checkNotNull(lens);
		analysis = XtaExplAnalysis.create(system);
		projection = s -> s;
	}

	@Override
	public Analysis<ExplState, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public Function<ExplState, ?> getProjection() {
		return projection;
	}

	@Override
	public boolean mightCover(final ArgNode<S, XtaAction> coveree, final ArgNode<S, XtaAction> coverer) {
		assert lens.get(coveree.getState()).equals(lens.get(coverer.getState()));
		return true;
	}

	@Override
	public void cover(final ArgNode<S, XtaAction> coveree, final ArgNode<S, XtaAction> coverer,
					  final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats) {
	}

	@Override
	public void block(final ArgNode<S, XtaAction> node, final XtaAction action, final S succState,
					  final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats) {
		assert lens.get(succState).isBottom();
	}

}
