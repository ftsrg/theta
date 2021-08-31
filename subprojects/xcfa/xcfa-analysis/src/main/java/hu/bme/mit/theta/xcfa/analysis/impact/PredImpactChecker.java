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
package hu.bme.mit.theta.xcfa.analysis.impact;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.BasicMultiStackableExprState;
import hu.bme.mit.theta.analysis.expr.BasicStackableExprState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.pred.PredAbstractors;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaAnalysis;
import hu.bme.mit.theta.xcfa.analysis.XcfaLocationState;
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.analysis.prec.GlobalXcfaPrec;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Map;
import java.util.function.Predicate;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static java.util.Collections.emptySet;

public final class PredImpactChecker implements SafetyChecker<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction, UnitPrec> {

	private final ImpactChecker<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction, UnitPrec> checker;

	private PredImpactChecker(final LTS<? super XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, ? extends XcfaAction> lts, final Map<Integer, XcfaLocation> initLocs,
							  final Predicate<Map<Integer, XcfaLocation>> targetLocs, final ItpSolver solver) {
		checkNotNull(lts);
		checkNotNull(initLocs);
		checkNotNull(solver);

		final Analysis<PredState, ExprAction, PredPrec> predAnalysis = PredAnalysis.create(solver,
				PredAbstractors.booleanSplitAbstractor(solver), True());

		final XcfaPrec<PredPrec> fixedPrec = GlobalXcfaPrec.create(PredPrec.of(emptySet()));

		final Analysis<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction, XcfaPrec<PredPrec>> cfaAnalysis = XcfaAnalysis.create(initLocs,
				predAnalysis);

		final Analysis<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction, UnitPrec> analysis = PrecMappingAnalysis.create(cfaAnalysis,
				np -> fixedPrec);

		final Predicate<XcfaState<?, ?, ?>> target = s -> targetLocs.test(s.getLocations());

		final ArgBuilder<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction, UnitPrec> argBuilder = ArgBuilder.create(lts, analysis,
				target);

		final ImpactRefiner<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction> refiner = PredImpactRefiner.create(solver);

		checker = ImpactChecker.create(argBuilder, refiner, XcfaState::getLocations);
	}

	public static PredImpactChecker create(final LTS<? super XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, ? extends XcfaAction> lts,
										   final Map<Integer, XcfaLocation> initLocs, final Predicate<Map<Integer, XcfaLocation>> targetLocs, final ItpSolver solver) {
		return new PredImpactChecker(lts, initLocs, targetLocs, solver);
	}

	@Override
	public SafetyResult<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction> check(final UnitPrec prec) {
		return checker.check(prec);
	}

}
