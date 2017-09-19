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
package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Optional;
import java.util.stream.Stream;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.common.Utils;

public final class ArgNode<S extends State, A extends Action> {

	private static final int HASH_SEED = 8543;
	private volatile int hashCode = 0;

	final ARG<S, A> arg;

	private final int id;
	private final int depth;
	private final boolean target;

	private S state;

	Optional<ArgEdge<S, A>> inEdge; // Set by ARG
	final Collection<ArgEdge<S, A>> outEdges;

	Optional<ArgNode<S, A>> coveringNode; // Set by ARG
	final Collection<ArgNode<S, A>> coveredNodes;

	boolean expanded; // Set by ArgBuilder

	ArgNode(final ARG<S, A> arg, final S state, final int id, final int depth, final boolean target) {
		this.arg = arg;
		this.state = state;
		this.id = id;
		this.depth = depth;
		this.target = target;
		inEdge = Optional.empty();
		outEdges = new ArrayList<>();
		coveringNode = Optional.empty();
		coveredNodes = new HashSet<>();
		expanded = false;
	}

	////

	public int getId() {
		return id;
	}

	/**
	 * Gets the depth of the node, which is 0 if the node has no parent, and
	 * depth(parent) + 1 otherwise.
	 */
	public int getDepth() {
		return depth;
	}

	public S getState() {
		return state;
	}

	public void setState(final S state) {
		checkNotNull(state);
		this.state = state;
	}

	public boolean mayCover(final ArgNode<S, A> node) {
		if (arg.domain.isLeq(node.getState(), this.getState())) {
			return ancestors().noneMatch(n -> n.equals(node) || n.isSubsumed());
		} else {
			return false;
		}
	}

	public void setCoveringNode(final ArgNode<S, A> node) {
		checkNotNull(node);
		checkArgument(node.arg == this.arg, "Nodes belong to different ARGs");
		unsetCoveringNode();
		coveringNode = Optional.of(node);
		node.coveredNodes.add(this);
	}

	public void unsetCoveringNode() {
		if (coveringNode.isPresent()) {
			coveringNode.get().coveredNodes.remove(this);
			coveringNode = Optional.empty();
		}
	}

	public void clearCoveredNodes() {
		coveredNodes.forEach(n -> n.coveringNode = Optional.empty());
		coveredNodes.clear();
	}

	public void cover(final ArgNode<S, A> node) {
		checkArgument(!node.isExcluded(), "Node is not excluded");
		final Collection<ArgNode<S, A>> oldCoveredNodes = new ArrayList<>(coveredNodes);
		descendants().forEach(ArgNode::clearCoveredNodes);
		setCoveringNode(node);
		oldCoveredNodes.forEach(n -> n.setCoveringNode(node));
	}

	////

	public Optional<ArgNode<S, A>> getParent() {
		return inEdge.map(ArgEdge::getSource);
	}

	public Optional<ArgEdge<S, A>> getInEdge() {
		return inEdge;
	}

	public Stream<ArgEdge<S, A>> getOutEdges() {
		return outEdges.stream();
	}

	public Optional<ArgNode<S, A>> getCoveringNode() {
		return coveringNode;
	}

	public Stream<ArgNode<S, A>> getCoveredNodes() {
		return coveredNodes.stream();
	}

	////

	public Stream<ArgNode<S, A>> getSuccNodes() {
		return getOutEdges().map(ArgEdge::getTarget);
	}

	public Stream<S> getSuccStates() {
		return getSuccNodes().map(ArgNode::getState);
	}

	////

	/**
	 * Checks if the node is covered, i.e., there is a covering edge for the
	 * node.
	 */
	public boolean isCovered() {
		return coveringNode.isPresent();
	}

	/**
	 * Checks if the node is not a bottom state.
	 */
	public boolean isFeasible() {
		return !arg.domain.isBottom(state);
	}

	/**
	 * Checks if the node is subsumed, i.e., the node is covered or not
	 * feasible.
	 */
	public boolean isSubsumed() {
		return isCovered() || !isFeasible();
	}

	/**
	 * Checks if the node is excluded, i.e., the node is subsumed or has an
	 * excluded parent.
	 */
	public boolean isExcluded() {
		return ancestors().anyMatch(ArgNode::isSubsumed);
	}

	/**
	 * Checks if the node is target, i.e., the target predicate holds (e.g., it
	 * is an error state).
	 */
	public boolean isTarget() {
		return target;
	}

	/**
	 * Checks if the node is expanded, i.e., all of its successors are present.
	 */
	public boolean isExpanded() {
		return expanded;
	}

	/**
	 * Checks if the node is leaf, i.e., it has no successors.
	 */
	public boolean isLeaf() {
		return outEdges.isEmpty();
	}

	/**
	 * Checks if the node is safe, i.e., not target or excluded.
	 */
	public boolean isSafe() {
		return !isTarget() || isExcluded();
	}

	/**
	 * Checks if the node is complete, i.e., expanded or excluded.
	 */
	public boolean isComplete() {
		return isExpanded() || isExcluded();
	}

	////

	public Stream<ArgNode<S, A>> properAncestors() {
		return getParent().map(p -> Stream.concat(Stream.of(p), p.properAncestors())).orElse(Stream.empty());
	}

	public Stream<ArgNode<S, A>> ancestors() {
		return Stream.concat(Stream.of(this), this.properAncestors());
	}

	public Stream<ArgNode<S, A>> children() {
		return outEdges.stream().map(ArgEdge::getTarget);
	}

	public Stream<ArgNode<S, A>> properDescendants() {
		return Stream.concat(this.children(), this.children().flatMap(ArgNode::properDescendants));
	}

	public Stream<ArgNode<S, A>> descendants() {
		return Stream.concat(Stream.of(this), this.properDescendants());
	}

	public Stream<ArgNode<S, A>> unexcludedDescendants() {
		if (this.isExcluded()) {
			return Stream.empty();
		} else {
			return unexcludedDescendantsOfNode();
		}
	}

	private Stream<ArgNode<S, A>> unexcludedDescendantsOfNode() {
		if (this.isSubsumed()) {
			return Stream.empty();
		} else {
			return Stream.concat(Stream.of(this), this.children().flatMap(ArgNode::unexcludedDescendantsOfNode));
		}
	}

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + id;
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		return super.equals(obj);
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder("ArgNode").add(id).add(state).toString();
	}

}
