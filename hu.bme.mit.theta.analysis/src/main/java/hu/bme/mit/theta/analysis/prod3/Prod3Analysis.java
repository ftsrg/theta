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
package hu.bme.mit.theta.analysis.prod3;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;

public final class Prod3Analysis<S1 extends State, S2 extends State, S3 extends State, A extends Action, P1 extends Prec, P2 extends Prec, P3 extends Prec>
		implements Analysis<Prod3State<S1, S2, S3>, A, Prod3Prec<P1, P2, P3>> {

	private final PartialOrd<Prod3State<S1, S2, S3>> partialOrd;
	private final InitFunc<Prod3State<S1, S2, S3>, Prod3Prec<P1, P2, P3>> initFunc;
	private final TransFunc<Prod3State<S1, S2, S3>, A, Prod3Prec<P1, P2, P3>> transFunc;

	private Prod3Analysis(final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2,
			final Analysis<S3, ? super A, P3> analysis3) {
		checkNotNull(analysis1);
		checkNotNull(analysis2);
		checkNotNull(analysis3);
		partialOrd = Prod3Ord.create(analysis1.getPartialOrd(), analysis2.getPartialOrd(), analysis3.getPartialOrd());
		initFunc = Prod3InitFunc.create(analysis1.getInitFunc(), analysis2.getInitFunc(), analysis3.getInitFunc());
		transFunc = Prod3TransFunc.create(analysis1.getTransFunc(), analysis2.getTransFunc(), analysis3.getTransFunc());
	}

	public static <S1 extends State, S2 extends State, S3 extends State, A extends Action, P1 extends Prec, P2 extends Prec, P3 extends Prec> Prod3Analysis<S1, S2, S3, A, P1, P2, P3> create(
			final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2,
			final Analysis<S3, ? super A, P3> analysis3) {
		return new Prod3Analysis<>(analysis1, analysis2, analysis3);
	}

	@Override
	public PartialOrd<Prod3State<S1, S2, S3>> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<Prod3State<S1, S2, S3>, Prod3Prec<P1, P2, P3>> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<Prod3State<S1, S2, S3>, A, Prod3Prec<P1, P2, P3>> getTransFunc() {
		return transFunc;
	}

}
