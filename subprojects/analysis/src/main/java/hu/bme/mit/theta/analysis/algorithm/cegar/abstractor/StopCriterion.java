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
package hu.bme.mit.theta.analysis.algorithm.cegar.abstractor;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;

import java.util.Collection;

/**
 * Interface for stopping criterions during abstraction.
 */
public interface StopCriterion<S extends State, A extends Action> {
	/**
	 * Check if abstraction can stop based on the whole ARG.
	 * @param arg ARG
	 * @return True if abstraction can stop
	 */
	boolean canStop(ARG<S, A> arg);

	/**
	 * Check if abstraction can stop based on the whole ARG or based on
	 * the new successor nodes (optimization: the whole ARG might not be needed).
	 * @param arg ARG
	 * @param newNodes New successor nodes
	 * @return True if abstraction can stop
	 */
	boolean canStop(ARG<S, A> arg, Collection<ArgNode<S, A>> newNodes);
}
