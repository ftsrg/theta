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
package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

/**
 * Represents a compisite node of the visualizable graph.
 */
public final class CompositeNode extends Node {

	private final Collection<Node> children;

	CompositeNode(final String id, final NodeAttributes attributes) {
		super(id, attributes);
		this.children = new ArrayList<Node>();
	}

	void addChild(final Node child) {
		checkNotNull(child);
		checkArgument(child != this);
		checkArgument(child.getParent() == null);

		children.add(child);
		child.setParent(this);
	}

	public Collection<Node> getChildren() {
		return Collections.unmodifiableCollection(children);
	}
}
