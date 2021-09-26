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
package hu.bme.mit.theta.analysis.zone;

import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;

import java.util.Collection;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public final class ZonePrec implements Prec {

	private final Set<VarDecl<RatType>> clocks;

	private ZonePrec(final Collection<? extends VarDecl<RatType>> clocks) {
		checkNotNull(clocks);
		this.clocks = ImmutableSet.copyOf(clocks);
	}

	public static ZonePrec of(final Collection<? extends VarDecl<RatType>> clocks) {
		return new ZonePrec(clocks);
	}

	public Set<VarDecl<RatType>> getVars() {
		return clocks;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).addAll(clocks).toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ZonePrec) {
			final ZonePrec that = (ZonePrec) obj;
			return this.getVars().equals(that.getVars());
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return 31 * clocks.hashCode();
	}

	@Override
	public Collection<VarDecl<?>> getUsedVars() { // This could be way more elegant
		return clocks.stream().map(ratTypeVarDecl -> (VarDecl<?>)ratTypeVarDecl).collect(Collectors.toSet());
	}
}
