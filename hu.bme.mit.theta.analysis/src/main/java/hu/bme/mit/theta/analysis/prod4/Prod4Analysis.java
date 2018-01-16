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
package hu.bme.mit.theta.analysis.prod4;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;

public final class Prod4Analysis<S1 extends State, S2 extends State, S3 extends State, S4 extends State, A extends Action, P1 extends Prec, P2 extends Prec, P3 extends Prec, P4 extends Prec>
		implements Analysis<Prod4State<S1, S2, S3, S4>, A, Prod4Prec<P1, P2, P3, P4>> {

	private final PartialOrd<Prod4State<S1, S2, S3, S4>> partialOrd;
	private final InitFunc<Prod4State<S1, S2, S3, S4>, Prod4Prec<P1, P2, P3, P4>> initFunc;
	private final TransFunc<Prod4State<S1, S2, S3, S4>, A, Prod4Prec<P1, P2, P3, P4>> transFunc;

	private Prod4Analysis(final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2,
			final Analysis<S3, ? super A, P3> analysis3, final Analysis<S4, ? super A, P4> analysis4) {
		checkNotNull(analysis1);
		checkNotNull(analysis2);
		checkNotNull(analysis3);
		checkNotNull(analysis4);
		partialOrd = Prod4Ord.create(analysis1.getPartialOrd(), analysis2.getPartialOrd(), analysis3.getPartialOrd(),
				analysis4.getPartialOrd());
		initFunc = Prod4InitFunc.create(analysis1.getInitFunc(), analysis2.getInitFunc(), analysis3.getInitFunc(),
				analysis4.getInitFunc());
		transFunc = Prod4TransFunc.create(analysis1.getTransFunc(), analysis2.getTransFunc(), analysis3.getTransFunc(),
				analysis4.getTransFunc());
	}

	public static <S1 extends State, S2 extends State, S3 extends State, S4 extends State, A extends Action, P1 extends Prec, P2 extends Prec, P3 extends Prec, P4 extends Prec> Prod4Analysis<S1, S2, S3, S4, A, P1, P2, P3, P4> create(
			final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2,
			final Analysis<S3, ? super A, P3> analysis3, final Analysis<S4, ? super A, P4> analysis4) {
		return new Prod4Analysis<>(analysis1, analysis2, analysis3, analysis4);
	}

	@Override
	public PartialOrd<Prod4State<S1, S2, S3, S4>> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<Prod4State<S1, S2, S3, S4>, Prod4Prec<P1, P2, P3, P4>> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<Prod4State<S1, S2, S3, S4>, A, Prod4Prec<P1, P2, P3, P4>> getTransFunc() {
		return transFunc;
	}

}
