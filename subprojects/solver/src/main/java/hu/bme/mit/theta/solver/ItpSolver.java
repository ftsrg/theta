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
package hu.bme.mit.theta.solver;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import com.google.common.collect.Lists;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public interface ItpSolver extends Solver {

	ItpPattern createPattern(final ItpMarker marker);

	default ItpPattern createBinPattern(final ItpMarker markerA, final ItpMarker markerB) {
		checkNotNull(markerA);
		checkNotNull(markerB);

		return createSeqPattern(Arrays.asList(markerA, markerB));
	}

	default ItpPattern createSeqPattern(final List<? extends ItpMarker> markers) {
		checkNotNull(markers);
		checkArgument(!markers.isEmpty());

		ItpPattern result = null;
		ItpPattern current = null;

		for (final ItpMarker marker : Lists.reverse(markers)) {
			if (result == null) {
				current = createPattern(marker);
				result = current;
			} else {
				current = current.createChild(marker);
			}
		}
		return result;
	}

	ItpMarker createMarker();

	void add(final ItpMarker marker, final Expr<BoolType> assertion);

	default void add(final ItpMarker marker, final Iterable<? extends Expr<BoolType>> assertions) {
		checkNotNull(marker);
		checkNotNull(assertions);
		for (final Expr<BoolType> assertion : assertions) {
			add(marker, assertion);
		}
	}

	Interpolant getInterpolant(final ItpPattern pattern);

	Collection<? extends ItpMarker> getMarkers();

}
