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
 * Represents a simple node of the visualizable graph.
 */
public class Node {

	private final String id;
	private final NodeAttributes attributes;

	private final Collection<Edge> inEdges;
	private final Collection<Edge> outEdges;

	private Node parent;

	Node(final String id, final NodeAttributes attributes) {
		this.id = checkNotNull(id);
		this.attributes = checkNotNull(attributes);
		this.inEdges = new ArrayList<>();
		this.outEdges = new ArrayList<>();
		this.parent = null;
	}

	public String getId() {
		return id;
	}

	public NodeAttributes getAttributes() {
		return attributes;
	}

	public Collection<Edge> getInEdges() {
		return Collections.unmodifiableCollection(inEdges);
	}

	public Collection<Edge> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}

	/**
	 * Add an outgoing edge. The source of the edge must be set to this node.
	 *
	 * @param edge
	 */
	void addOutEdge(final Edge edge) {
		checkArgument(edge.getSource() == this, "The source of the edge must be set to this node.");
		outEdges.add(edge);
	}

	/**
	 * Add an incoming edge. The target of the edge must be set to this node.
	 *
	 * @param edge
	 */
	void addInEdge(final Edge edge) {
		checkArgument(edge.getTarget() == this, "The target of the edge must be set to this node.");
		inEdges.add(edge);
	}

	public Node getParent() {
		return parent;
	}

	void setParent(final Node parent) {
		this.parent = parent;
	}

	public boolean isRoot() {
		return getParent() == null;
	}

}
