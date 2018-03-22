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
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAnalysis;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics.Builder;

final class CombinedStrategy<S1 extends State, S2 extends State>
		implements AlgorithmStrategy<XtaState<Prod2State<S1, S2>>, XtaState<Prod2State<S1, S2>>> {

	private final AlgorithmStrategy<XtaState<Prod2State<S1, S2>>, S1> strategy1;
	private final AlgorithmStrategy<XtaState<Prod2State<S1, S2>>, S2> strategy2;
	private final Analysis<XtaState<Prod2State<S1, S2>>, XtaAction, UnitPrec> analysis;
	private final Function<XtaState<Prod2State<S1, S2>>, ?> projection;

	public CombinedStrategy(final XtaSystem system, final AlgorithmStrategy<XtaState<Prod2State<S1, S2>>, S1> strategy1,
			final AlgorithmStrategy<XtaState<Prod2State<S1, S2>>, S2> strategy2) {
		this.strategy1 = checkNotNull(strategy1);
		this.strategy2 = checkNotNull(strategy2);
		this.analysis = createAnalysis(system);
		projection = s -> Tuple3.of(strategy1.getProjection().apply(s.getState().getState1()),
				strategy2.getProjection().apply(s.getState().getState2()), s.getLocs());
	}

	@Override
	public Analysis<XtaState<Prod2State<S1, S2>>, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public Function<XtaState<Prod2State<S1, S2>>, ?> getProjection() {
		return projection;
	}

	@Override
	public boolean mightCover(final ArgNode<XtaState<Prod2State<S1, S2>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod2State<S1, S2>>, XtaAction> coverer) {
		return strategy1.mightCover(coveree, coverer) && strategy2.mightCover(coveree, coverer);
	}

	@Override
	public void cover(final ArgNode<XtaState<Prod2State<S1, S2>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod2State<S1, S2>>, XtaAction> coverer,
			final Collection<ArgNode<XtaState<Prod2State<S1, S2>>, XtaAction>> uncoveredNodes, final Builder stats) {
		assert coveree.getCoveringNode().isPresent() && coveree.getCoveringNode().get().equals(coverer);
		strategy1.cover(coveree, coverer, uncoveredNodes, stats);
		if (coveree.isCovered()) {
			strategy2.cover(coveree, coverer, uncoveredNodes, stats);
		}
	}

	@Override
	public void block(final ArgNode<XtaState<Prod2State<S1, S2>>, XtaAction> node, final XtaAction action,
			final XtaState<Prod2State<S1, S2>> succState,
			final Collection<ArgNode<XtaState<Prod2State<S1, S2>>, XtaAction>> uncoveredNodes, final Builder stats) {
		assert succState.isBottom();
		if (succState.getState().isBottom1()) {
			strategy1.block(node, action, succState, uncoveredNodes, stats);
		} else if (succState.getState().isBottom2()) {
			strategy2.block(node, action, succState, uncoveredNodes, stats);
		} else {
			throw new AssertionError();
		}
	}

	////

	private Analysis<XtaState<Prod2State<S1, S2>>, XtaAction, UnitPrec> createAnalysis(final XtaSystem system) {
		final Analysis<S1, XtaAction, UnitPrec> analysis1 = strategy1.getAnalysis();
		final Analysis<S2, XtaAction, UnitPrec> analysis2 = strategy2.getAnalysis();
		final Analysis<Prod2State<S1, S2>, XtaAction, Prod2Prec<UnitPrec, UnitPrec>> prodAnalysis = Prod2Analysis
				.create(analysis1, analysis2);
		final Analysis<XtaState<Prod2State<S1, S2>>, XtaAction, Prod2Prec<UnitPrec, UnitPrec>> xtaAnalysis = XtaAnalysis
				.create(system, prodAnalysis);
		final Prod2Prec<UnitPrec, UnitPrec> prec = Prod2Prec.of(UnitPrec.getInstance(), UnitPrec.getInstance());
		final Analysis<XtaState<Prod2State<S1, S2>>, XtaAction, UnitPrec> analysis = PrecMappingAnalysis
				.create(xtaAnalysis, p -> prec);
		return analysis;
	}

}
