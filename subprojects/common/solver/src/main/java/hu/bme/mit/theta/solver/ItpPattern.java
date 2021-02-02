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

import java.util.Collection;

/**
 * Interface for an element of an interpolation pattern.
 * For example, in sequence interpolation the patterns form a linear chain.
 */
public interface ItpPattern {

	/**
	 * Get the current marker.
	 *
	 * @return Marker
	 */
	ItpMarker getMarker();

	/**
	 * Get the parent pattern.
	 *
	 * @return Parent
	 */
	ItpPattern getParent();

	/**
	 * Get child patterns.
	 *
	 * @return Children
	 */
	Collection<ItpPattern> getChildren();

	/**
	 * Create a child for the current pattern with a given marker.
	 *
	 * @param marker Marker
	 * @return Child
	 */
	ItpPattern createChild(final ItpMarker marker);

}
