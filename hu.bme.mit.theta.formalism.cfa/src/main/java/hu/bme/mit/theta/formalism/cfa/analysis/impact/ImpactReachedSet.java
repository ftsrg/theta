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
package hu.bme.mit.theta.formalism.cfa.analysis.impact;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.reachedset.ReachedSet;

public final class ImpactReachedSet<S extends State, A extends Action, K> implements ReachedSet<S, A> {

	private final Function<? super S, ? extends K> partitioning;

	private final Map<K, List<ArgNode<S, A>>> partitions;

	private ImpactReachedSet(final Function<? super S, ? extends K> partitioning) {
		this.partitioning = checkNotNull(partitioning);
		partitions = new HashMap<>();
	}

	public static <S extends State, A extends Action, K> ImpactReachedSet<S, A, K> create(
			final Function<? super S, ? extends K> partitioning) {
		return new ImpactReachedSet<>(partitioning);
	}

	@Override
	public void add(final ArgNode<S, A> node) {
		checkNotNull(node);
		final S state = node.getState();
		final K key = partitioning.apply(state);
		final Collection<ArgNode<S, A>> partition = partitions.computeIfAbsent(key, k -> new ArrayList<>());
		partition.add(node);
	}

	@Override
	public void tryToCover(final ArgNode<S, A> node) {
		checkNotNull(node);
		final S state = node.getState();
		final K key = partitioning.apply(state);
		final Collection<ArgNode<S, A>> partition = partitions.getOrDefault(key, Collections.emptyList());
		for (final ArgNode<S, A> nodeToCoverWith : partition) {
			if (nodeToCoverWith.getId() < node.getId()) {
				if (nodeToCoverWith.mayCover(node)) {
					node.cover(nodeToCoverWith);
					return;
				}
			} else {
				return;
			}
		}
	}

}
