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
package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunc;

final class Prod3TransferFunc<S1 extends State, S2 extends State, S3 extends State, A extends Action, P1 extends Prec, P2 extends Prec, P3 extends Prec>
		implements TransferFunc<Prod3State<S1, S2, S3>, A, Prod3Prec<P1, P2, P3>> {

	private final TransferFunc<S1, ? super A, P1> transferFunc1;
	private final TransferFunc<S2, ? super A, P2> transferFunc2;
	private final TransferFunc<S3, ? super A, P3> transferFunc3;

	private Prod3TransferFunc(final TransferFunc<S1, ? super A, P1> transferFunc1,
			final TransferFunc<S2, ? super A, P2> transferFunc2, final TransferFunc<S3, ? super A, P3> transferFunc3) {
		this.transferFunc1 = checkNotNull(transferFunc1);
		this.transferFunc2 = checkNotNull(transferFunc2);
		this.transferFunc3 = checkNotNull(transferFunc3);
	}

	public static <S1 extends State, S2 extends State, S3 extends State, A extends Action, P1 extends Prec, P2 extends Prec, P3 extends Prec> Prod3TransferFunc<S1, S2, S3, A, P1, P2, P3> create(
			final TransferFunc<S1, ? super A, P1> transferFunc1, final TransferFunc<S2, ? super A, P2> transferFunc2,
			final TransferFunc<S3, ? super A, P3> transferFunc3) {
		return new Prod3TransferFunc<>(transferFunc1, transferFunc2, transferFunc3);
	}

	@Override
	public Collection<? extends Prod3State<S1, S2, S3>> getSuccStates(final Prod3State<S1, S2, S3> state,
			final A action, final Prod3Prec<P1, P2, P3> prec) {
		checkNotNull(state);
		checkNotNull(prec);

		final Collection<? extends S1> succStates1 = transferFunc1.getSuccStates(state._1(), action, prec._1());
		final Collection<? extends S2> succStates2 = transferFunc2.getSuccStates(state._2(), action, prec._2());
		final Collection<? extends S3> succStates3 = transferFunc3.getSuccStates(state._3(), action, prec._3());
		return ProdState.product(succStates1, succStates2, succStates3);
	}

}
