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

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;

import java.util.Objects;

public final class ArgEdge<S extends State, A extends Action> {
	private static final int HASH_SEED = 3653;
	private volatile int hashCode = 0;

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		ArgEdge<?, ?> argEdge = (ArgEdge<?, ?>) o;
		return Objects.equals(source.getState(), argEdge.source.getState())
				&& Objects.equals(target.getState(), argEdge.target.getState())
				&& Objects.equals(action.toString(), argEdge.action.toString());
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + source.getState().hashCode();
			result = 31 * result + target.getState().hashCode();
			result = 31 * result + action.toString().hashCode();
			hashCode = result;
		}
		return result;
		// return Objects.hash(source.getState(), target.getState(), action.toString());
	}

	private final ArgNode<S, A> source;
	private final ArgNode<S, A> target;
	private final A action;

	ArgEdge(final ArgNode<S, A> source, final A action, final ArgNode<S, A> target) {
		this.source = source;
		this.action = action;
		this.target = target;
	}

	public ArgNode<S, A> getSource() {
		return source;
	}

	public ArgNode<S, A> getTarget() {
		return target;
	}

	public A getAction() {
		return action;
	}

}
