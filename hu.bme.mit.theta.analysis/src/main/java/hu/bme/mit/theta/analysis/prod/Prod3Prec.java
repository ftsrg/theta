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
import hu.bme.mit.theta.common.product.Product3;

public final class Prod3Prec<P1 extends Prec, P2 extends Prec, P3 extends Prec> extends ProdPrec
		implements Product3<P1, P2, P3> {

	Prod3Prec(final P1 prec1, final P2 prec2, final P3 prec3) {
		super(ImmutableList.of(prec1, prec2, prec3));
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

	@Override
	public P3 _3() {
		@SuppressWarnings("unchecked")
		final P3 result = (P3) elem(2);
		return result;
	}

}
