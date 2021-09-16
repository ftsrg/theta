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
package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.Prec;

import java.util.Map;

public final class XcfaPrec<P extends Prec> implements Prec {
	private final P globalPrec;
	private final Map<Integer, P> localPrecs;

	private XcfaPrec(final P globalPrec, final Map<Integer, P> localPrecs) {
		this.globalPrec = globalPrec;
		this.localPrecs = localPrecs;
	}

	public static <P extends Prec> XcfaPrec<P> create(final P globalPrec, final Map<Integer, P> localPrecs) {
		return new XcfaPrec<P>(globalPrec, localPrecs);
	}

	public P getPrec(final Integer key) {
		return localPrecs.get(key);
	}

	public P getGlobalPrec() {
		return globalPrec;
	}
}
