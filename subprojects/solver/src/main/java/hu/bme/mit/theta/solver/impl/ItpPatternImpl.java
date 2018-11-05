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
package hu.bme.mit.theta.solver.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;

public class ItpPatternImpl implements ItpPattern {

	private ItpPattern parent;
	private final List<ItpPattern> children;

	private final ItpMarker marker;

	public ItpPatternImpl(final ItpMarker marker) {
		this.marker = checkNotNull(marker);
		children = new LinkedList<>();
	}

	@Override
	public ItpMarker getMarker() {
		return marker;
	}

	@Override
	public ItpPattern getParent() {
		return parent;
	}

	@Override
	public Collection<ItpPattern> getChildren() {
		return Collections.unmodifiableCollection(children);
	}

	@Override
	public ItpPattern createChild(final ItpMarker marker) {
		checkNotNull(marker);
		final ItpPatternImpl child = new ItpPatternImpl(marker);
		children.add(child);
		child.parent = this;
		return child;
	}

}
