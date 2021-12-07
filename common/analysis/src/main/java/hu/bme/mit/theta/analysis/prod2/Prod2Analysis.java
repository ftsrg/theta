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
package hu.bme.mit.theta.analysis.prod2;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;

public final class Prod2Analysis<S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec>
		implements Analysis<Prod2State<S1, S2>, A, Prod2Prec<P1, P2>> {

	private final PartialOrd<Prod2State<S1, S2>> partialOrd;
	private final InitFunc<Prod2State<S1, S2>, Prod2Prec<P1, P2>> initFunc;
	private final TransFunc<Prod2State<S1, S2>, A, Prod2Prec<P1, P2>> transFunc;

	private Prod2Analysis(final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2,
						  final PreStrengtheningOperator<S1, S2> preStrengtheningOperator,
						  final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator) {
		checkNotNull(analysis1);
		checkNotNull(analysis2);
		partialOrd = Prod2Ord.create(analysis1.getPartialOrd(), analysis2.getPartialOrd());
		initFunc = Prod2InitFunc.create(analysis1.getInitFunc(), analysis2.getInitFunc(), strenghteningOperator);
		transFunc = Prod2TransFunc.create(analysis1.getTransFunc(), analysis2.getTransFunc(), preStrengtheningOperator, strenghteningOperator);
	}

	public static <S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec> Prod2Analysis<S1, S2, A, P1, P2> create(
			final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2) {
		return create(analysis1, analysis2, DefaultPreStrengtheningOperator.create(), (states, prec) -> states);
	}

	public static <S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec> Prod2Analysis<S1, S2, A, P1, P2> create(
			final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2,
			final PreStrengtheningOperator<S1, S2> preStrengtheningOperator,
			final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator) {
		return new Prod2Analysis<>(analysis1, analysis2, preStrengtheningOperator, strenghteningOperator);
	}

	@Override
	public PartialOrd<Prod2State<S1, S2>> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<Prod2State<S1, S2>, Prod2Prec<P1, P2>> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<Prod2State<S1, S2>, A, Prod2Prec<P1, P2>> getTransFunc() {
		return transFunc;
	}

}
