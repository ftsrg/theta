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

import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;

import java.util.Collection;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public final class Prod3Prec<P1 extends Prec, P2 extends Prec, P3 extends Prec> implements Prec {
	private static final int HASH_SEED = 4073;
	private volatile int hashCode = 0;

	private final P1 prec1;
	private final P2 prec2;
	private final P3 prec3;

	private Prod3Prec(final P1 prec1, final P2 prec2, final P3 prec3) {
		this.prec1 = checkNotNull(prec1);
		this.prec2 = checkNotNull(prec2);
		this.prec3 = checkNotNull(prec3);
	}

	public static <P1 extends Prec, P2 extends Prec, P3 extends Prec> Prod3Prec<P1, P2, P3> of(final P1 prec1,
																							   final P2 prec2, final P3 prec3) {
		return new Prod3Prec<>(prec1, prec2, prec3);
	}

	public P1 getPrec1() {
		return prec1;
	}

	public P2 getPrec2() {
		return prec2;
	}

	public P3 getPrec3() {
		return prec3;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 37 * result + prec1.hashCode();
			result = 37 * result + prec2.hashCode();
			result = 37 * result + prec3.hashCode();
			result = hashCode;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof Prod3Prec) {
			final Prod3Prec<?, ?, ?> that = (Prod3Prec<?, ?, ?>) obj;
			return this.prec1.equals(that.prec1) && this.prec2.equals(that.prec2) && this.prec3.equals(that.prec3);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder("Prod3Prec").add(prec1).add(prec2).add(prec3).toString();
	}

	@Override
	public Collection<VarDecl<?>> getUsedVars() {
		return Streams.concat(prec1.getUsedVars().stream(), prec2.getUsedVars().stream(), prec3.getUsedVars().stream()).collect(Collectors.toSet());
	}
}
