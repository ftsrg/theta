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

import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics.Builder;

interface AlgorithmStrategy<S1 extends State, S2 extends State> {

	Analysis<S2, XtaAction, UnitPrec> getAnalysis();

	Function<S2, ?> getProjection();

	boolean mightCover(final ArgNode<S1, XtaAction> coveree, ArgNode<S1, XtaAction> coverer);

	void cover(ArgNode<S1, XtaAction> coveree, ArgNode<S1, XtaAction> coverer,
			Collection<ArgNode<S1, XtaAction>> uncoveredNodes, final Builder stats);

	void block(ArgNode<S1, XtaAction> node, final XtaAction action, final S1 succState,
			Collection<ArgNode<S1, XtaAction>> uncoveredNodes, final Builder stats);

}
