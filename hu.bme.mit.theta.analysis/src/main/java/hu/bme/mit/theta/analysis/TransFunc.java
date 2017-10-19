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
package hu.bme.mit.theta.analysis;

import java.util.Collection;

/**
 * Common interface for transfer functions.
 */
@FunctionalInterface
public interface TransFunc<S extends State, A extends Action, P extends Prec> {
	/**
	 * Gets successor states of a state with a given action and precision.
	 * 
	 * @param state
	 * @param action
	 * @param prec
	 * @return Collection of successor states
	 */
	Collection<? extends S> getSuccStates(S state, A action, P prec);

}
