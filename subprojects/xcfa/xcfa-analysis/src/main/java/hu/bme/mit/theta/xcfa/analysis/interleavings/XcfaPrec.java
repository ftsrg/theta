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
package hu.bme.mit.theta.xcfa.analysis.interleavings;

import hu.bme.mit.theta.analysis.Prec;

public final class XcfaPrec<P extends Prec> implements Prec {
	private final P globalPrec;

	private XcfaPrec(final P globalPrec) {
		this.globalPrec = globalPrec;
	}

	public static <P extends Prec> XcfaPrec<P> create(final P globalPrec) {
		return new XcfaPrec<P>(globalPrec);
	}

	public P getGlobalPrec() {
		return globalPrec;
	}

	public XcfaPrec<P> refine(P runningPrec) {
		if (this.globalPrec.equals(runningPrec)) {
			return this;
		} else {
			return create(runningPrec);
		}
	}
}
