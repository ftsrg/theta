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

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Represents a directed edge of the visualizable graph.
 */
public final class Edge {

	private final Node source;
	private final Node target;
	private final EdgeAttributes attributes;

	/**
	 * Create a new edge. The edge adds itself to the outgoing/incoming edges of
	 * the source/target node.
	 *
	 * @param source
	 * @param target
	 * @param attributes
	 */
	Edge(final Node source, final Node target, final EdgeAttributes attributes) {
		this.source = checkNotNull(source);
		this.target = checkNotNull(target);
		this.attributes = checkNotNull(attributes);
		source.addOutEdge(this);
		target.addInEdge(this);
	}

	public Node getSource() {
		return source;
	}

	public Node getTarget() {
		return target;
	}

	public EdgeAttributes getAttributes() {
		return attributes;
	}

}
