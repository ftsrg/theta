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
package hu.bme.mit.theta.analysis.expr.refinement;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.utils.IndexedVars;

/**
 * A variable-based refutation that is a sequence of sets of variables.
 */
public final class VarsRefutation implements Refutation {

	private final IndexedVars indexedVars;
	private final int pruneIndex;

	private VarsRefutation(final IndexedVars indexedVars) {
		checkNotNull(indexedVars);
		checkArgument(!indexedVars.isEmpty(), "Trying to create refutation with empty set of variables");
		this.indexedVars = indexedVars;
		int i = 0;
		while (indexedVars.getVars(i).isEmpty()) {
			++i;
		}
		this.pruneIndex = i;
	}

	public static VarsRefutation create(final IndexedVars indexedVars) {
		return new VarsRefutation(indexedVars);
	}

	public IndexedVars getVarSets() {
		return indexedVars;
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder(getClass().getSimpleName()).add(indexedVars).toString();
	}

	@Override
	public int getPruneIndex() {
		return pruneIndex;
	}
}
