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
package hu.bme.mit.theta.xcfa.analysis.prec;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Represents an immutable global precision that maps the same precision to each
 * location. A refiner is also implemented.
 *
 * @see GlobalXcfaPrecRefiner
 */
public final class GlobalXcfaPrec<P extends Prec> implements XcfaPrec<P> {

	private final P prec;

	private GlobalXcfaPrec(final P prec) {
		this.prec = checkNotNull(prec);
	}

	public static <P extends Prec> GlobalXcfaPrec<P> create(final P prec) {
		return new GlobalXcfaPrec<>(prec);
	}

	public GlobalXcfaPrec<P> refine(final P refinedPrec) {
		if (this.prec.equals(refinedPrec)) {
			return this;
		} else {
			return create(refinedPrec);
		}
	}

	@Override
	public P getPrec(final XcfaLocation loc) {
		checkNotNull(loc);
		return prec;
	}

	public P getPrec() {
		return prec;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).add(prec).toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof GlobalXcfaPrec) {
			final GlobalXcfaPrec<?> that = (GlobalXcfaPrec<?>) obj;
			return this.prec.equals(that.prec);
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return 31 * prec.hashCode();
	}

}
