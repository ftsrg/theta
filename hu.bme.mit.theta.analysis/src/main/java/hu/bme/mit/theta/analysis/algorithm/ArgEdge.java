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

public final class ArgEdge<S extends State, A extends Action> {

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
