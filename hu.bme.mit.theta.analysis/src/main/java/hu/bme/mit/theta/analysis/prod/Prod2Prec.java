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

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.product.Product2;

public final class Prod2Prec<P1 extends Prec, P2 extends Prec> extends ProdPrec implements Product2<P1, P2> {

	private Prod2Prec(final P1 prec1, final P2 prec2) {
		super(ImmutableList.of(prec1, prec2));
	}

	public static <P1 extends Prec, P2 extends Prec> Prod2Prec<P1, P2> of(final P1 prec1, final P2 prec2) {
		return new Prod2Prec<>(prec1, prec2);
	}

	@Override
	public P1 _1() {
		@SuppressWarnings("unchecked")
		final P1 result = (P1) elem(0);
		return result;
	}

	@Override
	public P2 _2() {
		@SuppressWarnings("unchecked")
		final P2 result = (P2) elem(1);
		return result;
	}

}
